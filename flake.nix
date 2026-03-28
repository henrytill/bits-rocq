{
  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";
    flake-utils.url = "github:numtide/flake-utils";
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
      nixpkgs,
      flake-utils,
      ...
    }:
    flake-utils.lib.eachDefaultSystem (
      system:
      let
        pkgs = nixpkgs.legacyPackages.${system};

        coqPkgs = pkgs.coqPackages_9_0;
        roqPkgs = pkgs.rocqPackages;
        ocamlPkgs = coqPkgs.coq.ocamlPackages;

        bits-rocq = ocamlPkgs.buildDunePackage {
          pname = "bits-rocq";
          version = "0.0.0-dev";
          src = self;
          duneVersion = "3";
          nativeBuildInputs = [
            ocamlPkgs.menhir
            coqPkgs.coq
          ];
          buildInputs = [
            roqPkgs.rocq-core
            roqPkgs.stdlib
            roqPkgs.mathcomp-boot
            roqPkgs.mathcomp-order
            roqPkgs.hierarchy-builder
            roqPkgs.rocq-elpi
            coqPkgs.equations
            coqPkgs.MenhirLib
            ocamlPkgs.zarith
          ];
          checkInputs = with ocamlPkgs; [
            alcotest
            ppx_deriving
            ppx_import
          ];
          doCheck = true;
        };
      in
      {
        packages.default = bits-rocq;
        devShells.default = pkgs.mkShell {
          inputsFrom = [ bits-rocq ];
        };
      }
    );
}
