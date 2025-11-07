{
  stdenv,
  cmake,
  omnilink,
  omnilink_models,
  msgpack-cxx,

  ghUrl ? "git@github.com:ubc-systopia/augmented-chromatic-trees.git",
  ghRev,
  setbenchSubdir,
}:
let
  setbenchSrc = builtins.fetchGit {
    url = ghUrl;
    rev = ghRev;
  };
in
stdenv.mkDerivation {
  pname = "setbench-workload";
  version = ghRev;
  dontStrip = true;
  srcs = [
    setbenchSrc
    ./workload
  ];
  buildInputs = [
    omnilink.lib
    msgpack-cxx
    omnilink_models.SetBench
  ];
  nativeBuildInputs = [
    cmake
  ];
  env.SETBENCH_SUBDIR = setbenchSubdir;
  sourceRoot = "workload";
  postInstall = ''
    chmod a+x $out/bin/main
  '';
}