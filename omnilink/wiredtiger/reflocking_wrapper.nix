{
  omnilink,
  omnilink_models,
  cmake,
  stdenv,
  msgpack-cxx,
}:
stdenv.mkDerivation {
  version = "0.1.0";
  pname = "reflocking-wrapper";
  src = ./reflocking_wrapper;
  buildInputs = [
    omnilink.lib
    omnilink_models.RefLocking
    msgpack-cxx
  ];
  nativeBuildInputs = [
    cmake
  ];
}