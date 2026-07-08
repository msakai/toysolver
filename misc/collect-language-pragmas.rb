require 'pathname'

base = ARGV[0] || "."
exts = {}

Dir.glob("**/*.hs", base: base){|fname|
  src = File.read(File.join(base, fname), encoding: "utf-8")
  src.scan(/{-# LANGUAGE([^#]*)#-}/){
    $1.strip().split(/\s*,\s*/).each{|ext|
      (exts[ext] ||= []).push fname
    }
  }
}

exts.keys.sort.each{|ext|
  puts ext
  exts[ext].each{|fname|
    puts "  #{fname}"
  }
}
