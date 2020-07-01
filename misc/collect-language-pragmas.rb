require 'pathname'

base = ARGV[0] || "."
exts = []

Dir.glob("**/*.hs", base: base){|fname|
  src = File.read(File.join(base, fname))
  src.scan(/{-# LANGUAGE([^#]*)#-}/){
    exts.concat($1.strip().split(/\s*,\s*/))
  }
}

exts.sort.uniq.each{|ext|
  puts ext
}
