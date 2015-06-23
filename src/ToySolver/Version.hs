{-# LANGUAGE CPP, TemplateHaskell #-}
module ToySolver.Version
  ( version
  , packageVersions
  , gitHash
  ) where

import Data.List
import Data.Version
import qualified ToySolver.Internal.GitHash as GitHash
import Paths_toysolver

packageVersions :: [(String, String)]
packageVersions = sort $ tail
  [ (undefined, undefined) -- dummy
#ifdef VERSION_OptDir
  , ("OptDir",       VERSION_OptDir       )
#endif
#ifdef VERSION_array
  , ("array",        VERSION_array        )
#endif
#ifdef VERSION_base
  , ("base",         VERSION_base         )
#endif
#ifdef VERSION_bytestring
  , ("bytestring",   VERSION_bytestring   )
#endif
#ifdef VERSION_bytestring_builder
  , ("bytestring-builder",   VERSION_bytestring_builder   )
#endif
#ifdef VERSION_containers
  , ("containers",   VERSION_containers   )
#endif
#ifdef VERSION_data_interval
  , ("data-interval", VERSION_data_interval)
#endif
#ifdef VERSION_data_default_class
  , ("data-default-class", VERSION_data_default_class)
#endif
#ifdef VERSION_deepseq
  , ("deepseq",      VERSION_deepseq      )
#endif
#ifdef VERSION_exceptions
  , ("exceptions",   VERSION_exceptions   )
#endif
#ifdef VERSION_extended_reals
  , ("extended-reals", VERSION_extended_reals)
#endif
#ifdef VERSION_filepath
  , ("filepath",     VERSION_filepath     )
#endif
#ifdef VERSION_finite_field
  , ("finite-field", VERSION_finite_field )
#endif
#ifdef VERSION_hashable
  , ("hashable",     VERSION_hashable     )
#endif
#ifdef VERSION_heaps
  , ("heaps",        VERSION_heaps        )
#endif
#ifdef VERSION_intern
  , ("intern",       VERSION_intern       )
#endif
#ifdef VERSION_loop
  , ("loop",         VERSION_loop         )
#endif
#ifdef VERSION_mtl
  , ("mtl",          VERSION_mtl          )
#endif
#ifdef VERSION_multiset
  , ("multiset",     VERSION_multiset     )
#endif
#ifdef VERSION_mwc_random
  , ("mwc-random",   VERSION_mwc_random   )
#endif
#ifdef VERSION_old_locale
  , ("old_locale",   VERSION_old_locale   )
#endif
#ifdef VERSION_parse_dimacs
  , ("parse_dimacs", VERSION_parse_dimacs )
#endif
#ifdef VERSION_parsec
  , ("parsec",       VERSION_parsec       )
#endif
#ifdef VERSION_prettyclass
  , ("prettyclass",  VERSION_prettyclass  )
#endif
#ifdef VERSION_primes
  , ("primes",       VERSION_primes       )
#endif
#ifdef VERSION_process
  , ("process",      VERSION_process      )
#endif
#ifdef VERSION_pseudo_boolean
  , ("pseudo-boolean", VERSION_pseudo_boolean)
#endif
#ifdef VERSION_queue
  , ("queue",        VERSION_queue        )
#endif
#ifdef VERSION_sign
  , ("sign",         VERSION_sign         )
#endif
#ifdef VERSION_stm
  , ("stm",          VERSION_stm          )
#endif
#ifdef VERSION_temporary
  , ("temporary",    VERSION_time         )
#endif
#ifdef VERSION_time
  , ("time",         VERSION_time         )
#endif
#ifdef VERSION_type_level_numbers
  , ("type-level-numbers", VERSION_type_level_numbers)
#endif
#ifdef VERSION_unbounded_delays
  , ("unbounded-delays", VERSION_unbounded_delays)
#endif
#ifdef VERSION_unordered_containers
  , ("unordered-containers", VERSION_unordered_containers)
#endif
#ifdef VERSION_vector_space
  , ("vector-space", VERSION_vector_space)
#endif
#ifdef VERSION_logic_TPTP
  , ("logic-TPTP",   VERSION_logic_TPTP   )
#endif
  ]

gitHash :: Maybe String
gitHash = $(GitHash.gitHashQ)
