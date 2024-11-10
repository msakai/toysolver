require 'pathname'

base = ARGV[0] || "."

h = {}

Dir.glob("**/*.hs", base: base){|fname|
  File.open(fname, encoding: "utf-8"){|f|
    f.each_line{|l|
      if /MIN_VERSION_\w+\(\d+,\d+,\d+\)/ =~ l
        (h[$~[0]] ||= []) << fname
      end
    }
  }
}

h.keys.sort.each {|k|
  puts k
  h[k].each {|fname|
    puts "  #{fname}"
  }
}
