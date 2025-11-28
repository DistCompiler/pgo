let
  pkgs = import <nixpkgs> {
    overlays = [
      (import ../static_overlay.nix)
    ];
  };
in pkgs.omnilink.lib
