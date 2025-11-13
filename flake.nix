{
  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";
    opam-repository = {
      url = "github:ocaml/opam-repository";
      flake = false;
    };
    rocq-opam = {
      url = "github:rocq-prover/opam";
      flake = false;
    };
    opam-nix = {
      url = "github:tweag/opam-nix";
      inputs.nixpkgs.follows = "nixpkgs";
      inputs.opam-repository.follows = "opam-repository";
    };
    flake-utils = {
      follows = "opam-nix/flake-utils";
    };
  };
  nixConfig = {
    extra-substituters = [ "https://henrytill.cachix.org" ];
    extra-trusted-public-keys = [
      "henrytill.cachix.org-1:EOoUIk8e9627viyFmT6mfqghh/xtfnpzEtqT4jnyn1M="
    ];
  };
  outputs =
    {
      self,
      flake-utils,
      opam-nix,
      nixpkgs,
      opam-repository,
      rocq-opam,
      ...
    }@inputs:
    let
      package = "bits-rocq";
    in
    flake-utils.lib.eachDefaultSystem (
      system:
      let
        pkgs = nixpkgs.legacyPackages.${system};
        repos = [
          "${opam-repository}"
          "${rocq-opam}/released"
        ];
        on = opam-nix.lib.${system};
        scope =
          on.buildOpamProject
            {
              inherit repos;
              resolveArgs.with-test = true;
            }
            package
            ./.
            {
              ocaml-base-compiler = "5.3.0";
            };
        overlay = final: prev: { ${package} = prev.${package}.overrideAttrs (as: { }); };
      in
      {
        legacyPackages = scope.overrideScope overlay;
        packages.default = self.legacyPackages.${system}.${package};
        devShells.default = pkgs.mkShell {
          inputsFrom = [ self.legacyPackages.${system}.${package} ];
        };
      }
    );
}
