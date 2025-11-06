{
  msgpack-cxx,
  cmake,
  stdenv,
}:
stdenv.mkDerivation (finalAttrs: {
  pname = "omnilink";
  version = "0.1.0";
  src = ./.;
  buildInputs = [
    msgpack-cxx
  ];
  nativeBuildInputs = [
    cmake
  ];
})
