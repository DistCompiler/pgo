{
  stdenv,
  python3,
  swig,
  cmake,
  pkg-config,
  fetchFromGitHub,
  omnilink,
  msgpack-cxx,

  ghOwner ? "wiredtiger",
  ghRepo ? "wiredtiger",
  ghHash ? "",
  ghRev,
}:
let
  src = fetchFromGitHub {
    owner = ghOwner;
    repo = ghRepo;
    rev = ghRev;
    hash = ghHash;
  };
in
stdenv.mkDerivation {
  version = ghRev;
  pname = "wiredtiger";
  dontStrip = true;
  env.NIX_CFLAGS_COMPILE = "-Wno-error"; # or we get strange fireworks!
  cmakeFlags = [
    # unbreak .pc file
    "-DCMAKE_INSTALL_LIBDIR=lib"
    "-DCMAKE_INSTALL_INCLUDEDIR=include"
    # debug build in case something goes wrong
    "-DCMAKE_BUILD_TYPE=Debug"
    # allows us to extract wtperf
    "-DENABLE_STATIC=ON"
    "-DENABLE_SHARED=OFF"
  ];
  buildInputs = [
    python3
    swig
    omnilink.lib
    msgpack-cxx
    omnilink.wiredtiger.reflocking_wrapper
  ];
  nativeBuildInputs = [
    cmake
    pkg-config
  ];
  src = src;
  postInstall = ''
    cp bench/wtperf/wtperf $out/bin/wtperf
  '';
}