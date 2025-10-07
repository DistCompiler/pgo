{
  description = "OmniLink SetBench Stressor";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
  };

  outputs = { nixpkgs, ... }:
    let
      pkgs = nixpkgs.legacyPackages.x86_64-linux;
    in {
      systems = [ "x86_64-linux" ];
      packages.x86_64-linux.default = pkgs.stdenv.mkDerivation {
        name = "setbench-stressor";
        buildInputs = [
          pkgs.msgpack-cxx
        ];
        src = ./.;
      };
    };
}
