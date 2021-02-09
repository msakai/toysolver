# Script for fixing the ld.exe path issue of GHC 8.10.2 on x86_64-windows
# https://gitlab.haskell.org/ghc/ghc/-/issues/18550
require 'pathname'

ghc_root = Pathname.new(`stack.exe path --compiler-bin`.strip).parent
settings_path = ghc_root / "lib" / "settings"

broken_path = "C:/GitLabRunner/builds/2WeHDSFP/0/ghc/ghc/inplace/mingw/bin/ld.exe"
correct_path = (ghc_root / "mingw" / "bin" / "ld.exe").to_s.gsub(/\\/, '/')

s = File.binread(settings_path)
if s.gsub!(broken_path, correct_path)
  puts "Fixing broken ld path in #{settings_path.to_s}: #{broken_path} -> #{correct_path}"
  settings_path.rename(settings_path.sub_ext(".bak"))
  File.binwrite(settings_path, s)
end
