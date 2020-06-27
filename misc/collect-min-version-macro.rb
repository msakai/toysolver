require 'pathname'

base = ARGV[0] || "."

a = []

Dir.glob("**/*.hs", base: base){|fname|
  File.open(fname){|f|
    f.each_line{|l|
      if /MIN_VERSION_\w+\(\d+,\d+,\d+\)/ =~ l
        a << $~[0]
      end
    }
  }
}

a.sort.uniq.each{|l|
  puts l
}
