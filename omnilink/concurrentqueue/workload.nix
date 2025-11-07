{
  stdenv,
  cmake,
  omnilink,
  omnilink_models,
  msgpack-cxx,

  m_concurrentqueue ? omnilink.concurrentqueue.lib.v1_0_4,
}:
stdenv.mkDerivation {
  pname = "concurrentqueue-workload";
  version = "0.1.0";
  src = ./workload;
  dontStrip = true;
  buildInputs = [
    omnilink.lib
    m_concurrentqueue
    msgpack-cxx
    omnilink_models.ConcurrentQueueAPI
  ];
  nativeBuildInputs = [
    cmake
  ];
  postInstall = ''
    chmod a+x $out/bin/main
  '';
}