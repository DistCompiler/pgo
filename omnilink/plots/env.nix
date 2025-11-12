{
  mkShell,
  python313Packages,
  python313
}:
mkShell {
  packages = [
    python313Packages.matplotlib
    python313
  ];
}
