{
  stdenv,
  python3,
  swig,
  cmake,
  pkg-config,
  fetchFromGitHub,

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
  env.NIX_CFLAGS_COMPILE = "-Wno-error"; # or we get strange fireworks!
  cmakeFlags = [
    # unbreak .pc file
    "-DCMAKE_INSTALL_LIBDIR=lib"
    "-DCMAKE_INSTALL_INCLUDEDIR=include"
    # debug build in case something goes wrong
    "-DCMAKE_BUILD_TYPE=Debug"
  ];
  buildInputs = [
    python3
    swig
  ];
  nativeBuildInputs = [
    cmake
    pkg-config
  ];
  src = src;
}