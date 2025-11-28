#pragma once

#include "pack.hpp"
#include <algorithm>
#include <array>
#include <atomic>
#include <cassert>
#include <csignal>
#include <cstddef>
#include <cstdint>
#include <cstdlib>
#include <cstring>
#include <fcntl.h>
#include <filesystem>
#include <iostream>
#include <sstream>
#include <string_view>
#include <thread>
#include <unistd.h>
#include <variant>

#include <msgpack.hpp>

#include <omnilink/pack.hpp>

namespace omnilink {

struct outstream {
  virtual void write(const char *data, std::size_t count) = 0;
};

// This uses raw syscalls permitted in signal handlers (per POSIX),
// both to avoid any buffering issues, and so we can run e.g.,
// during a segfault, from a signal handler.
struct outstream_sigsafe : public outstream {
  outstream_sigsafe(const char *file) {
    // second param is permission bits. I pasted them from POSIX manual, hope
    // they are right.
    fd = open(file, O_WRONLY | O_CREAT | O_TRUNC,
              S_IRUSR | S_IWUSR | S_IRGRP | S_IROTH);
    if (fd == -1) {
      std::cerr << "Error opening " << file << " " << strerror(errno)
                << std::endl;
      std::abort();
    }
  }

  outstream_sigsafe(const outstream_sigsafe &) = delete;
  outstream_sigsafe &operator=(const outstream_sigsafe &) = delete;

  void write(const char *data, std::size_t count) {
    assert(fd != -1);
    assert(data != nullptr);
    std::size_t pos = bytes_written.fetch_add(count);

    ssize_t written = 0;
    while (written < count) {
      ssize_t w =
          pwrite(fd, (void *)(data + written), count - written, pos + written);
      if (w == -1) {
        std::cerr << "Error writing " << (count - written)
                  << " bytes to log file [fd=" << fd << "] (" << strerror(errno)
                  << ")" << std::endl;
        std::abort();
      }
      written += w;
    }
  }

  ~outstream_sigsafe() {
    if (fd != -1) {
      close(fd);
    }
  }

private:
  int fd = -1;
  std::atomic<std::size_t> bytes_written = 0;
};

struct outstream_buffered {
  outstream_buffered(outstream &underlying) : underlying{underlying} {}

  struct atomic_writer_t : public outstream {
    atomic_writer_t(outstream_buffered &out) : out{out} {
      bool atomic_lock_actual = false;
      while (
          !out.atomic_lock.compare_exchange_strong(atomic_lock_actual, true)) {
        atomic_lock_actual = false;
        std::this_thread::yield();
      }
    }

    atomic_writer_t(const atomic_writer_t &) = delete;
    atomic_writer_t &operator=(const atomic_writer_t &) = delete;

    void write(const char *data, std::size_t count) {
      assert(data != nullptr);
      assert(count <= buffer_size_max);
      assert(count <= out.atomic_buffer_capacity());

      if (count > out.buffer_capacity()) {
        assert(out.atomic_bytes <= out.buffer_bytes);
        out.underlying.write(out.buffer.data(), out.atomic_bytes);
        std::copy(out.buffer.begin() + out.atomic_bytes,
                  out.buffer.begin() + out.buffer_bytes, out.buffer.begin());
        out.buffer_bytes -= out.atomic_bytes;
        out.atomic_bytes = 0;
      }

      assert(count <= out.buffer_capacity());
      std::copy(data, data + count, out.buffer.begin() + out.buffer_bytes);
      out.buffer_bytes += count;
    }

    ~atomic_writer_t() {
      assert(out.atomic_lock);
      out.atomic_lock = false;
      out.atomic_bytes = out.buffer_bytes;
    }

  private:
    outstream_buffered &out;
  };

  bool flush_signalsafe() {
    bool atomic_lock_actual = false;
    if (atomic_lock.compare_exchange_strong(atomic_lock_actual, true)) {
      underlying.write(buffer.data(), atomic_bytes);
      buffer_bytes -= atomic_bytes;
      atomic_bytes = 0;
      atomic_lock = false;
      return true;
    }
    return false;
  }

  atomic_writer_t atomic_writer() { return atomic_writer_t{*this}; }

  ~outstream_buffered() {
    if (!flush_signalsafe()) {
      std::cerr << "Failed to normally flush log contents" << std::endl;
    }
  }

private:
  outstream &underlying;
  std::atomic<bool> atomic_lock = false;
  std::size_t atomic_bytes = 0;

  static constexpr std::size_t buffer_size_max = 1024;
  std::size_t buffer_bytes = 0;
  std::array<char, buffer_size_max> buffer;

  std::size_t buffer_capacity() const {
    assert(buffer_bytes <= buffer.size());
    return buffer.size() - buffer_bytes;
  }

  std::size_t atomic_buffer_capacity() const {
    return buffer_size_max - (buffer_bytes - atomic_bytes);
  }
};

struct TerminateThread {
  static constexpr std::string_view _name_ = "__TerminateThread";
  bool _did_abort = false;
  uint64_t _op_start = 0, _op_end = 0;
  omnilink::Packable _meta;
  MSGPACK_DEFINE_MAP(_did_abort, _op_start, _op_end, _meta);
};

struct AbortThread {
  static constexpr std::string_view _name_ = "__AbortThread";
  bool _did_abort = false;
  uint64_t _op_start = 0, _op_end = 0;
  std::string_view signal;
  omnilink::Packable _meta;
  MSGPACK_DEFINE_MAP(_did_abort, _op_start, _op_end, signal, _meta);
};

template <typename AnyOperation> struct pretty_name_of {
  // static constexpr std::string_view value = "???";
};

static uint64_t get_timestamp_now() {
  // Thread local is ok, per link below.
  // This might work better from a C library, since static initialization
  // happens inside the function (and we can be called from a C library).
  static thread_local std::atomic<int> _dummy_var_for_mfence = 0;
  unsigned int lo, hi;
  _dummy_var_for_mfence.exchange(1); // prevent CPU reorderings
  // potentially faster than std::atomic_thread_fence
  // https://stackoverflow.com/questions/48316830/why-does-this-stdatomic-thread-fence-work
  __asm__ __volatile__("rdtsc" : "=a"(lo), "=d"(hi));
  _dummy_var_for_mfence.exchange(1); // prevent CPU reorderings
  return (((uint64_t)(hi & ~(1 << 31)) << 32) | lo);
}

template <typename... Operations> struct ActionRecord {
  std::string_view operation_name;
  std::variant<TerminateThread, AbortThread, Operations...> operation;

  uint64_t &op_start() {
    return std::visit([](auto &op) -> uint64_t & { return op._op_start; },
                      operation);
  }

  uint64_t &op_end() {
    return std::visit([](auto &op) -> uint64_t & { return op._op_end; },
                      operation);
  }

  Packable &meta() {
    return std::visit([](auto &op) -> Packable & { return op._meta; },
                      operation);
  }

  MSGPACK_DEFINE_MAP(operation_name, operation);
};

struct logger_iface {
  logger_iface() {}
  virtual ~logger_iface() {}
  virtual void handle_crash(int sig, const std::string_view &sig_name) = 0;
};

struct logger_handle {
  static_assert(std::atomic<std::size_t>::is_always_lock_free);

  logger_handle(logger_iface *iface) {
    handle = new handle_t(iface);

    auto next = first_handle().load();
    handle->next = next;

    while (!first_handle().compare_exchange_weak(next, handle)) {
      handle->next = next;
    }
  }

  template <typename F> static void foreach_iface(F f) {
    auto curr = first_handle().load();
    while (curr != nullptr) {
      // Lock the iface while we're looking at it, so the thread-local storage
      // can't be marked for deletion during actual usage of the iface ptr. This
      // can only block thread-local storage deallocation (since expected CAS
      // value is 1), and has no effect if the block should already be deleted.
      // Deleted blocks will just be skipped because the CAS failed.
      std::size_t is_alive_expected = 1;
      if (curr->is_alive.compare_exchange_strong(is_alive_expected, 2)) {
        assert(curr->iface != nullptr);
        f(curr->iface);
        auto next = curr->next.load();
        curr->is_alive = is_alive_expected;
        curr = next;
      } else {
        curr = curr->next.load();
      }
    }
  }

  logger_iface *get_ptr() const {
    assert(handle != nullptr);
    auto iface = handle->iface;
    assert(iface != nullptr);
    return iface;
  }

  ~logger_handle() {
    std::size_t expected_is_alive = 1;
    if (!handle->is_alive.compare_exchange_weak(expected_is_alive, 0)) {
      assert(expected_is_alive == 2);
      // Under concurrent access from signal handler, just give up.
      // We are currently segfaulting and memory reclamation is not a concern.
      return;
    }

    // Best effort to clean up thread data for dead threads.
    // We can at least be sure that no-one will try to access the iface ptr.
    auto iface = handle->iface;
    handle->iface = nullptr;
    delete iface;

    // Here we could write a sophisticated memory reclamation algorithm that
    // somehow eventually reclaims handle_t instances. We didn't technically
    // leak them anyway (we have a list of them), but this is a resource leak
    // if you allocate lots of threads that log.
    // TODO: do better
  }

private:
  struct handle_t {
    logger_iface *iface = nullptr;
    std::atomic<std::size_t> is_alive = 1;
    std::atomic<handle_t *> next = nullptr;

    handle_t(logger_iface *iface) : iface{iface} {}
  };
  static_assert(std::atomic<std::size_t>::is_always_lock_free);
  static_assert(std::atomic<handle_t *>::is_always_lock_free);

  static std::atomic<handle_t *> &first_handle() {
    static std::atomic<handle_t *> impl = nullptr;
    return impl;
  }
  handle_t *handle = nullptr;
};

template <typename AnyOperation> struct logger {};

template <typename... Operations>
struct logger<std::variant<Operations...>> : private logger_iface {
  static logger &instance() {
    static thread_local logger_handle inst{new logger{get_init_timestamp()}};
    return *(logger *)inst.get_ptr();
  }

  template <typename Operation> static Operation &start_operation() {
    auto &inst = instance();
    auto &current_record = inst.current_record;
    current_record.operation_name = Operation::_name_;
    current_record.operation.template emplace<Operation>();
    auto ts = get_timestamp_now();
    current_record.op_start() = ts;
    inst.last_timestamp = ts;
    return ongoing_operation<Operation>();
  }

  template <typename Operation> static Operation &ongoing_operation() {
    auto &inst = instance();
    auto &current_record = inst.current_record;
    return std::get<Operation>(current_record.operation);
  }

  static void mark_operation_start() {
    auto &inst = instance();
    auto ts = get_timestamp_now();
    inst.current_record.op_start() = ts;
    inst.last_timestamp = ts;
  }

  static void mark_operation_end() {
    auto &inst = instance();
    auto &op_end = inst.current_record.op_end();
    if (op_end == 0) {
      op_end = get_timestamp_now();
      inst.last_timestamp = op_end;
    }
  }

  template <typename Operation> static void end_operation() {
    auto &inst = instance();
    auto &current_record = inst.current_record;
    assert(std::holds_alternative<Operation>(current_record.operation));

    mark_operation_end();
    assert(current_record.op_start() <= current_record.op_end());

    auto w = inst.log_out.atomic_writer();
    msgpack::pack(w, current_record);
  }

  void handle_crash(int sig, const std::string_view &sig_name) override {
    std::cerr << "Received " << sig_name << ", flushing logs for " << tid
              << std::endl;
    if (!log_out.flush_signalsafe()) {
      std::cerr << "Could not flush log for " << tid << " due to contention."
                << std::endl;
    }
    ActionRecord<Operations...> rec;
    rec.operation = AbortThread{};
    auto &op = std::get<AbortThread>(rec.operation);
    op.signal = sig_name;
    rec.operation_name = AbortThread::_name_;
    op._op_start = last_timestamp.load();
    op._op_end = get_timestamp_now();

    outstream_buffered out{out_raw};
    auto w = out.atomic_writer();
    msgpack::pack(w, rec);
  }

private:
  static uint64_t &get_init_timestamp() {
    static uint64_t init_timestamp = get_timestamp_now();
    return init_timestamp;
  }

  const uint64_t &init_timestamp;
  logger(uint64_t &init_timestamp)
      : init_timestamp{init_timestamp}, out_raw{log_path().c_str()} {}

  const std::thread::id tid = std::this_thread::get_id();
  std::string log_filename() {
    auto &pretty_name = pretty_name_of<std::variant<Operations...>>::value;
    std::ostringstream out;
    out << "tracing-" << pretty_name << "-" << tid << ".log";
    auto s = out.str();
    std::cerr << "Writing trace to " << s << std::endl;
    return s;
  }
  std::filesystem::path log_path() {
    const char *dir = std::getenv("OMNILINK_TRACE_DIR");
    if (dir) {
      return std::filesystem::path(dir) / log_filename();
    } else {
      return std::filesystem::current_path() / log_filename();
    }
  }

  outstream_sigsafe out_raw;
  outstream_buffered log_out{out_raw};
  ActionRecord<Operations...> current_record;

  std::atomic<uint64_t> last_timestamp = get_timestamp_now();
};

extern "C" {

static void crash_handler(int sig) {
  std::string_view sig_name = "???";
  switch (sig) {
  case SIGSEGV:
    sig_name = "SIGSEGV";
    break;
  case SIGFPE:
    sig_name = "SIGFPE";
    break;
  case SIGILL:
    sig_name = "SIGILL";
    break;
  }
  logger_handle::foreach_iface([&](logger_iface *logger) -> void {
    logger->handle_crash(sig, sig_name);
  });
  std::abort();
}
}

} // namespace omnilink
