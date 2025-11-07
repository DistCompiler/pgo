{
  omnilink,
  omnilink_models,
  cmake,
  stdenv,
  pkg-config,
  msgpack-cxx,

  m_wiredtiger ? omnilink.wiredtiger.lib.v11_3_1,
}:
stdenv.mkDerivation {
  version = "0.1.0";
  pname = "wiredtiger-stressor";
  dontStrip = true;
  src = ./workload;
  buildInputs = [
    omnilink.lib
    omnilink_models.Storage
    m_wiredtiger
    msgpack-cxx
  ];
  nativeBuildInputs = [
    cmake
    pkg-config
  ];
  postInstall = ''
    chmod a+x $out/bin/main
  '';
}