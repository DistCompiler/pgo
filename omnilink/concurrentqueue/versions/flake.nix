{
  description = "ConcurrentQueue for OmniLink";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    concurrentqueue_1_0_4 = {
      type = "github";
      owner = "cameron314";
      repo = "concurrentqueue";
      rev = "6dd38b8a1dbaa7863aa907045f32308a56a6ff5d";
      flake = false;
    };
  };

  outputs = { nixpkgs, concurrentqueue_1_0_4, ... }:
    let
      pkgs = nixpkgs.legacyPackages.x86_64-linux;
      derivationForSrc = { version, src }: pkgs.stdenv.mkDerivation {
        version = "1.0.4";
        pname = "concurrentqueue";
        hardeningDisable = [ "all" ];
        nativeBuildInputs = [
          pkgs.cmake
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
      };
    in {
      systems = [ "x86_64-linux" ];
      packages.x86_64-linux.v1_0_4 = derivationForSrc {
        version = "1.0.4";
        src = concurrentqueue_1_0_4;
      };
  };
}
