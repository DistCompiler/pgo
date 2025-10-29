{
  description = "OmniLink Plotting Environment";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
  };

  outputs = { nixpkgs, ... }:
    let
      pkgs = nixpkgs.legacyPackages.x86_64-linux;
    in {
      systems = [ "x86_64-linux" ];
      packages.x86_64-linux.default = pkgs.stdenv.mkDerivation {
        name = "omnilink-plotter";
        buildInputs = [
          pkgs.python313Packages.matplotlib
          pkgs.python313
        ];
        src = ./.;
      };
    };
}
