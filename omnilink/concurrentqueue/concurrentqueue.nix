{
  stdenv,
  fetchFromGitHub,
  cmake,

  ghOwner ? "cameron314",
  ghRepo ? "concurrentqueue",
  ghRev,
  ghHash ? "",
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
  pname = "concurrentqueue";
  version = ghRev;
  hardeningDisable = [ "all" ];
  nativeBuildInputs = [
    cmake
  ];
  src = src;
  configurePhase = ''
    mkdir ./build2
    pushd ./build2
    cmake ..
    popd
  '';
  buildPhase = ''
    cmake --build ./build2
  '';
  installPhase = ''
    cmake --install ./build2 --prefix $out
  '';
}