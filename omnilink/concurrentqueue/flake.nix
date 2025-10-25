{
  description = "OmniLink ConcurrentQueue Stressor";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    concurrentqueue.url = ./versions;
    concurrentqueue.inputs.nixpkgs.follows = "nixpkgs";
  };

  outputs = { nixpkgs, concurrentqueue, ... }:
    let
      pkgs = nixpkgs.legacyPackages.x86_64-linux;
      forCQVersion = { version, cq }: pkgs.stdenv.mkDerivation {
        version = version;
        pname = "concurrentqueue-stressor";
        buildInputs = [
          cq
          pkgs.msgpack-cxx
        ];
        nativeBuildInputs = [
          pkgs.cmake
        ];
      };
    in {
      systems = [ "x86_64-linux" ];
      packages.x86_64-linux.v1_0_4 = forCQVersion {
        version = "1.0.4";
        cq = concurrentqueue.packages.x86_64-linux.v1_0_4;
      };
    };
}
