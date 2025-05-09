{-# OPTIONS_HADDOCK show-extensions #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE TemplateHaskell #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.Version
-- Copyright   :  (c) Masahiro Sakai 2013
-- License     :  BSD-style
--
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  non-portable
--
-----------------------------------------------------------------------------
module ToySolver.Version
  ( version
  , packageVersions
  , gitHash
  , compilationTime
  ) where

import Data.List (sort)
import Data.Time
import Data.Version
import ToySolver.Version.TH
import Paths_toysolver

packageVersions :: [(String, String)]
packageVersions = sort $ tail
  [ (undefined, undefined) -- dummy
#ifdef VERSION_MIP
  , ("MIP", VERSION_MIP)
#endif
#ifdef VERSION_OptDir
  , ("OptDir", VERSION_OptDir)
#endif
#ifdef VERSION_ansi_wl_pprint
  , ("ansi-wl-pprint", VERSION_ansi_wl_pprint)
#endif
#ifdef VERSION_array
  , ("array", VERSION_array)
#endif
#ifdef VERSION_attoparsec
  , ("attoparsec", VERSION_attoparsec)
#endif
#ifdef VERSION_base
  , ("base", VERSION_base)
#endif
#ifdef VERSION_bytestring
  , ("bytestring", VERSION_bytestring)
#endif
#ifdef VERSION_bytestring_builder
  , ("bytestring-builder", VERSION_bytestring_builder)
#endif
#ifdef VERSION_bytestring_encoding
  , ("bytestring-encoding", VERSION_bytestring_encoding)
#endif
#ifdef VERSION_case_insensitive
  , ("case-insensitive", VERSION_case_insensitive)
#endif
#ifdef VERSION_clock
  , ("clock", VERSION_clock)
#endif
#ifdef VERSION_containers
  , ("containers", VERSION_containers)
#endif
#ifdef VERSION_data_default
  , ("data-default", VERSION_data_default)
#endif
#ifdef VERSION_data_default_class
  , ("data-default-class", VERSION_data_default_class)
#endif
#ifdef VERSION_data_interval
  , ("data-interval", VERSION_data_interval)
#endif
#ifdef VERSION_deepseq
  , ("deepseq", VERSION_deepseq)
#endif
#ifdef VERSION_directory
  , ("directory", VERSION_directory)
#endif
#ifdef VERSION_extended_reals
  , ("extended-reals", VERSION_extended_reals)
#endif
#ifdef VERSION_filepath
  , ("filepath", VERSION_filepath)
#endif
#ifdef VERSION_finite_field
  , ("finite-field", VERSION_finite_field)
#endif
#ifdef VERSION_ghc_prim
  , ("ghc-prim", VERSION_ghc_prim)
#endif
#ifdef VERSION_hashable
  , ("hashable", VERSION_hashable)
#endif
#ifdef VERSION_hashtables
  , ("hashtables", VERSION_hashtables)
#endif
#ifdef VERSION_haskeline
  , ("haskeline", VERSION_haskeline)
#endif
#ifdef VERSION_heaps
  , ("heaps", VERSION_heaps)
#endif
#ifdef VERSION_intern
  , ("intern", VERSION_intern)
#endif
#ifdef VERSION_lattices
  , ("lattices", VERSION_lattices)
#endif
#ifdef VERSION_log_domain
  , ("log-domain", VERSION_log_domain)
#endif
#ifdef VERSION_logic_TPTP
  , ("logic-TPTP", VERSION_logic_TPTP)
#endif
#ifdef VERSION_loop
  , ("loop", VERSION_loop)
#endif
#ifdef VERSION_megaparsec
  , ("megaparsec", VERSION_megaparsec)
#endif
#ifdef VERSION_mtl
  , ("mtl", VERSION_mtl)
#endif
#ifdef VERSION_multiset
  , ("multiset", VERSION_multiset)
#endif
#ifdef VERSION_mwc_random
  , ("mwc-random", VERSION_mwc_random)
#endif
#ifdef VERSION_optparse_applicative
  , ("optparse-applicative", VERSION_optparse_applicative)
#endif
#ifdef VERSION_parsec
  , ("parsec", VERSION_parsec)
#endif
#ifdef VERSION_pretty
  , ("pretty", VERSION_pretty)
#endif
#ifdef VERSION_primes
  , ("primes", VERSION_primes)
#endif
#ifdef VERSION_primitive
  , ("primitive", VERSION_primitive)
#endif
#ifdef VERSION_process
  , ("process", VERSION_process)
#endif
#ifdef VERSION_pseudo_boolean
  , ("pseudo-boolean", VERSION_pseudo_boolean)
#endif
#ifdef VERSION_queue
  , ("queue", VERSION_queue)
#endif
#ifdef VERSION_scientific
  , ("scientific", VERSION_scientific)
#endif
#ifdef VERSION_semigroups
  , ("semigroups", VERSION_semigroups)
#endif
#ifdef VERSION_sign
  , ("sign", VERSION_sign)
#endif
#ifdef VERSION_split
  , ("split", VERSION_split)
#endif
#ifdef VERSION_stm
  , ("stm", VERSION_stm)
#endif
#ifdef VERSION_template_haskell
  , ("template-haskell", VERSION_template_haskell)
#endif
#ifdef VERSION_temporary
  , ("temporary", VERSION_temporary)
#endif
#ifdef VERSION_text
  , ("text", VERSION_text)
#endif
#ifdef VERSION_time
  , ("time", VERSION_time)
#endif
#ifdef VERSION_transformers
  , ("transformers", VERSION_transformers)
#endif
#ifdef VERSION_transformers_compat
  , ("transformers-compat", VERSION_transformers_compat)
#endif
#ifdef VERSION_unbounded_delays
  , ("unbounded-delays", VERSION_unbounded_delays)
#endif
#ifdef VERSION_unordered_containers
  , ("unordered-containers", VERSION_unordered_containers)
#endif
#ifdef VERSION_vector
  , ("vector", VERSION_vector)
#endif
#ifdef VERSION_vector_space
  , ("vector-space", VERSION_vector_space)
#endif
#ifdef VERSION_xml_conduit
  , ("xml-conduit", VERSION_xml_conduit)
#endif
#ifdef VERSION_zlib
  , ("zlib", VERSION_zlib)
#endif
  ]

gitHash :: Maybe String
gitHash = $(gitHashQ)

compilationTime :: UTCTime
compilationTime = $(compilationTimeQ)
