final: prev: {
  omnilink = (prev.omnilink or {}) // {
    lib = final.callPackage ./lib/package.nix {};

    porcupine = final.callPackage ./porcupine/package.nix {};

    # WiredTiger
    wiredtiger = (prev.omnilink.wiredtiger or {}) // {
      lib.v11_3_1 = final.callPackage ./wiredtiger/wiredtiger.nix {
        ghRev = "05c56015a42154ac8145366678a4f8eb419b5933";
        ghHash = "sha256-K5cZZTvZaWR6gVXF+mHNh7nHxMqi9XaEpB2qsd/pay8=";
      };
      lib.lockbug = final.callPackage ./wiredtiger/wiredtiger.nix {
        ghOwner = "fhackett";
        ghRev = "4a4333a704783aaf86ea4f74edde41b3f91ae971";
        ghHash = "sha256-DmUBmICDBQl2+nMRSm3M0SkUhcFc39xaJh1/KHf094s=";
      };
      workload = final.callPackage ./wiredtiger/workload.nix { };
      reflocking_wrapper = final.callPackage ./wiredtiger/reflocking_wrapper.nix { };
    };

    # concurrentqueue
    concurrentqueue.lib.v1_0_4 = final.callPackage ./concurrentqueue/concurrentqueue.nix {
      ghRev = "6dd38b8a1dbaa7863aa907045f32308a56a6ff5d";
      ghHash = "sha256-MkhlDme6ZwKPuRINhfpv7cxliI2GU3RmTfC6O0ke/IQ=";
    };
    concurrentqueue.workload = final.callPackage ./concurrentqueue/workload.nix {};

    # SetBench
    setbench.workload = {
      brown_ext_chromatic_augment_lf = final.callPackage ./setbench/workload.nix {
        ghRev = "9a8c04ccdaefb2d4ab893367f7ff99a593d51aa6"; # main as of paper sub
        setbenchSubdir = "ds/brown_ext_chromatic_augment_lf";
      };
      wei_ext_vcas_bst_lf = final.callPackage ./setbench/workload.nix {
        ghRev = "9a8c04ccdaefb2d4ab893367f7ff99a593d51aa6"; # main as of paper sub
        setbenchSubdir = "ds/wei_ext_vcas_bst_lf";
      };
      arbel_int_bst_lf = final.callPackage ./setbench/workload.nix {
        ghRev = "9a8c04ccdaefb2d4ab893367f7ff99a593d51aa6"; # main as of paper sub
        setbenchSubdir = "ds/arbel_int_bst_lf";
      };
      blelloch_ext_btree_lf = final.callPackage ./setbench/workload.nix {
        ghRev = "9a8c04ccdaefb2d4ab893367f7ff99a593d51aa6"; # main as of paper sub
        setbenchSubdir = "ds/blelloch_ext_btree_lf";
      };
      ellen_augmented_ext_bst_lf = final.callPackage ./setbench/workload.nix {
        ghRev = "9a8c04ccdaefb2d4ab893367f7ff99a593d51aa6"; # main as of paper sub
        setbenchSubdir = "ds/ellen_augmented_ext_bst_lf";
      };
      brown_ext_chromatic_delegateSingle_lf = final.callPackage ./setbench/workload.nix {
        ghRev = "9a8c04ccdaefb2d4ab893367f7ff99a593d51aa6"; # main as of paper sub
        setbenchSubdir = "ds/brown_ext_chromatic_delegateSingle_lf";
      };
      brown_ext_chromatic_augment_lf_linbug1 = final.callPackage ./setbench/workload.nix {
        ghRev = "a99d464a7dd0e8958c2093b3143dc3f069803dc5";
        setbenchSubdir = "ds/brown_ext_chromatic_augment_lf";
      };
      brown_ext_chromatic_augment_lf_linbug2 = final.callPackage ./setbench/workload.nix {
        ghRev = "802fd478fb9f495789454a1011e5b768ae94c18e";
        setbenchSubdir = "ds/brown_ext_chromatic_augment_lf";
      };
      brown_ext_chromatic_augment_lf_linbug3 = final.callPackage ./setbench/workload.nix {
        ghRev = "e4c751792e4d98ac68b8a7d50b7964e09f942997";
        setbenchSubdir = "ds/brown_ext_chromatic_augment_lf";
      };
      brown_ext_chromatic_delegateSingle_lf_linbug1 = final.callPackage ./setbench/workload.nix {
        ghRev = "938927dac7a3e8e0b767a04f84f02ea03c316bd1";
        setbenchSubdir = "ds/brown_ext_chromatic_delegateSingle_lf";
      };
      brown_ext_chromatic_delegateSingle_lf_linbug2 = final.callPackage ./setbench/workload.nix {
        ghRev = "e430f0bfc274fc2e066663efaa76262b2f0b9c4a";
        setbenchSubdir = "ds/brown_ext_chromatic_delegateSingle_lf";
      };
    };
  };
}