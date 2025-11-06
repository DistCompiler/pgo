{
  stdenv,

  modelName,
  modelDir,
}:
stdenv.mkDerivation {
  pname = modelName;
  version = "0.1.0";
  src = modelDir;
  env.MODEL_NAME = modelName;
  installPhase = ''
    mkdir -p $out/include/omnilink/models
    cp $MODEL_NAME.hpp $out/include/omnilink/models/$MODEL_NAME.hpp
  '';
}