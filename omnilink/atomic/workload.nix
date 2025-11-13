{
  stdenv,
  cmake,
  omnilink,
  omnilink_models,
  msgpack-cxx,
}:
stdenv.mkDerivation {
  pname = "atomic-workload";
  version = "0.1.0";
  src = ./workload;
  dontStrip = true;
  buildInputs = [
    omnilink.lib
    msgpack-cxx
    omnilink_models.Atomic
  ];
  nativeBuildInputs = [
    cmake
  ];
  postInstall = ''
    chmod a+x $out/bin/main
  '';
}