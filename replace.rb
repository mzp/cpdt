#! /opt/local/bin/ruby -w
# -*- mode:ruby; coding:utf-8 -*-

def replace(path,old,new)
  content = File.read path
  File.open(path,"w"){|io|
    io.print content.gsub(/#{old}/i,new)
  }
end

File.readlines("words.txt").each do|line|
  old,new = line.strip.split ":",2

  puts "#{old} => #{new}"
  Dir.glob("src/*.v").each do|path|
    puts path
    replace path,old,new
  end
end
