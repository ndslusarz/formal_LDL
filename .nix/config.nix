let
  common-bundle = {
    formal-LDL.job = true;
  };
  push-branches = [ "main" ];
in {
  ## DO NOT CHANGE THIS
  format = "1.0.0";
  ## unless you made an automated or manual update
  ## to another supported format.

  ## The attribute to build from the local sources,
  ## either using nixpkgs data or the overlays located in `.nix/rocq-overlays`
  ## and `.nix/coq-overlays`
  ## Will determine the default main-job of the bundles defined below
  attribute = "formal-LDL";

  ## If you want to select a different attribute (to build from the local sources as well)
  ## when calling `nix-shell` and `nix-build` without the `--argstr job` argument
  # shell-attribute = "formal-LDL";

  ## Maybe the shortname of the library is different from
  ## the name of the nixpkgs attribute, if so, set it here:
  # pname = "formal-LDL";

  ## Lists the dependencies, phrased in terms of nix attributes.
  ## formal-LDL is not (yet) in nixpkgs, so its dependencies are declared
  ## in the manual overlay `.nix/rocq-overlays/formal-LDL` instead.
  # buildInputs = [ ];

  ## Indicate the relative location of your _CoqProject
  ## If not specified, it defaults to "_CoqProject"
  # coqproject = "_CoqProject";

  ## select an entry to build in the following `bundles` set
  ## defaults to "default"
  default-bundle = "9.1";

  ## write one `bundles.name` attribute set per
  ## alternative configuration
  ## When generating GitHub Action CI, one workflow file
  ## will be created per bundle

  bundles."9.1" = {
    inherit push-branches;
    rocqPackages = common-bundle // {
      rocq-core.override.version = "9.1";
      coq.override.version = "9.1";
      mathcomp.override.version = "2.5.0";
    };
  };

  ## Cachix caches to use in CI
  ## Below we list some standard ones
  cachix.coq = {};
  cachix.math-comp = {};
  cachix.coq-community = {};

  ## If you have write access to one of these caches you can
  ## provide the auth token or signing key through a secret
  ## variable on GitHub. Then, you should give the variable
  ## name here. For instance, coq-community projects can use
  ## the following line instead of the one above:
  # cachix.coq-community.authToken = "CACHIX_AUTH_TOKEN";

  ## Or if you have a signing key for a given Cachix cache:
  # cachix.my-cache.signingKey = "CACHIX_SIGNING_KEY"

  ## Note that here, CACHIX_AUTH_TOKEN and CACHIX_SIGNING_KEY
  ## are the names of secret variables. They are set in
  ## GitHub's web interface.
}
