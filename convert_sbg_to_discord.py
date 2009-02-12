#! /usr/bin/python

# I had a request to allow discord to use sbagen .sbg script files or to have a converter for them.
# This is the result.  Make it executable with chmod +x and then run it at ./convert_sbg_to_discord.py
# to get a short description of how to run it, a built in help file.
# It is crude, but works reasonably well on simple and explicit .sbg files.  For
# more complicated files it translates them but leaves incorrect values.  For really complex files, it
# chokes.  It translates pink noise as a repeat of a pink.wav, and spin as a phase voice.  Options are 
# commented and no translation takes place.  You can interpret the above to mean that after you run 
# this on sbg files you will have to edit the discord files for errors. ;-)

# This code is in the public domain.

import os
import string
import re
import sys

def convert_sbg_to_discord ():

  """  Convert an input file for sbagen into an input file for 
    discord (sort of)  :-) .
  """

  for line in sys.argv:
    print line
  if len(sys.argv) < 2:  # need at least an input file
    help ()  # exit with some instruction
  # check for options parse the command line arguments
  ii = 1
  if (cmp (sys.argv[ii], "-s") == 0
     or cmp (sys.argv[ii], "--separator") == 0):
    ii += 1
    separator = sys.argv [ii]
  else:
    separator = "''''"
  print separator
  ii += 1
  # parse the rest of the command line arguments as filenames
  input_filenames = []
  output_filename = None
  for index in xrange (ii, len (sys.argv)):
    if cmp (sys.argv [index] [-3:], "sbg")  == 0:
      input_filenames.append (sys.argv [index])
    elif cmp (sys.argv [index] [-7:], "discord")  == 0:
      output_filename = sys.argv [index]
  for filename in input_filenames:  # for every input file
    print filename
    convert_file (filename, len(input_filenames), output_filename, separator)


def help ():
  """ Print simple usage instructions for convert_sbg_to_discord.py. """

  print ("Usage for convert_sbg_to_discord.py is:")
  print ("convert_sbg_to_discord.py [option] sbg_filename(s) [discord filename]")
  print ("""only option is -s or --separator followed by a space and the separator string 
            you want enclosed in double quotes""")
  print ("""If you use a wildcard for the input sbg files the output files will be named
          the same with the .discord extension and the discord filename will be ignored""")
  print ("""If the input is a single sbg file the output file will be named
          the same with the .discord extension or if the the discord filename 
          is present it will be used""")
  print ("""Couple of examples:
          ./convert_sbg_to_discord.py -s "   " one.sbg two.discord 
            will convert one.sbg to two.discord using 3 spaces for a separator.
          ./convert_sbg_to_discord.py -s ",,," *.sbg
            will convert all sbg files into files of the same name with discord 
            instead of sbg as an extension using 3 commas for a separator.""")
  sys.exit()

def convert_file (inname = None, incount = 1, outname=None, sep = "''''"):
  """" Parse an sbg file and write the output to a discord file. """

  if (inname == None):
    print ("Cannot convert a blank name")
    help ()
  infile = open (inname, 'r')
  if incount > 1 or outname == None:
    outname = inname [:-4] + ".discord"
  outfile = open (outname, 'w')
  sequence_dict = {}
  aggregate_dict = {}
  play_list = []
  times = []
  inline = infile.readline()
  while len (inline) != 0:
    print inline
    if len(inline) > 0:
      offset = inline.find("#")
      if offset != -1:  # a comment somewhere in the line
        comment = inline [offset:]
        outfile.write (comment)
        inline = inline [:offset]  # save line besides comment
    inline.strip()  # all whitespace
    if len(inline) > 0:
      if inline[0] == "-":  # this is an option line
        outfile.write ("# " + inline + "\n")  # write option as comment
        inline = infile.readline()
        continue  # process next line
      elif inline.find (":") != -1:   # a sequence definition or play line
        if (inline[0].isalpha()
            and inline[:3] != "NOW"):  # sequence
          if inline.find ("{") == -1:   # not an aggregate sequence definition
            inlist = inline.split()
            while "-" in inlist:  # this is a silence indicator
              offset = inlist.index ("-")
              inlist.remove ("-")  # remove single dash
              inlist.insert (offset, "silence/0")
            if (cmp(inlist[0], "off:") == 0):  # ignore off 
              last_was_off = 1
              inline = infile.readline()
              continue  # process next line
            sequence_dict [ inlist[0][:-1] ] = []
            for sequence in inlist[1:]:
              voicelist = sequence.split ("/")
              name = voicelist [0]
              amp = voicelist [1]
              if cmp (name, "pink") == 0:  # pink noise
                outline = ("  repeat" + sep + "pink.wav" + sep + amp + sep + amp 
                                      + sep + ".5" + sep + ".5" + sep + "0" + sep + "1" + "\n")
                sequence_dict [ inlist[0][:-1] ].append (outline)
              elif name.find("silence") != -1:  # silence
                outline = ("  silence" + "\n")
                sequence_dict [ inlist[0][:-1] ].append (outline)
              elif (name.find("spin:") != -1):  # spin
                name = name[5:]
                if name.find ("+") != -1:
                  carrier, beat = name.split ("+")
                  beat = "+" + beat
                  outline = ("  phase" + sep + carrier + sep + beat + sep + amp + sep + "720" + "\n")
                  sequence_dict [ inlist[0][:-1] ].append (outline)
              elif (name.find("bell") != -1):  # bell
                if name.find ("+") != -1:
                  temp, carrier = name.split ("+")
                outline = ("  once" + sep + "tone.wav" + sep + amp + sep + amp 
                                      + sep + ".5" + sep + ".5" + sep + "0" + sep + "1"
                                      + sep + "0" + "\n")
                sequence_dict [ inlist[0][:-1] ].append (outline)
              else:  # must be a binaural beat
                if name.find ("+") != -1:
                  carrier, beat = name.split ("+")
                  beat = "+" + beat
                elif name.find ("-") != -1:
                  carrier, beat = name.split ("-")
                  beat = "-" + beat
                else:  # not recognized
                  print ("Didn't recognize this line as a sequence\n   %s" % inline)
                  inline = infile.readline()
                  continue  # process next line
                outline = ("  binaural" + sep + carrier + sep + beat + sep + amp + "\n")
                sequence_dict [ inlist[0][:-1] ].append (outline)
          elif inline.find ("{") != -1:   # an aggregate sequence definition
            inlist = inline.split()
            keyval = inlist[0][:-1]
            aggregate_dict [keyval] = []
            inline = infile.readline()
            while inline.find("}") == -1:
              if len(inline) > 0:
                offset = inline.find("#")
                if offset != -1:  # a comment somewhere in the line
                  comment = inline [offset:]
                  outfile.write (comment)
                  inline = inline [:offset]  # save line besides comment
              inline.strip()  # all whitespace
              if len(inline) > 0:
                inlist = inline.split()
                print inlist
                subtimes = inlist[0].split(":")
                if len(subtimes) == 3:
                  times.append (3600*int(subtimes[0]) + 60*int(subtimes[1]) + int(subtimes[2]))
                elif len(subtimes) == 2:
                  times.append (3600*int(subtimes[0]) + 60*int(subtimes[1]))
                elif len(subtimes) == 1:
                  times.append (3600*int(subtimes[0]))
                print times
                if len (inlist) == 3:
                  if (inlist [1] == "=="
                      or inlist [1] == "<>"
                      or inlist [1] == "--"):
                    aggregate_dict [ keyval ].append ([times [-1], inlist[2]])
                    aggregate_dict [ keyval ].append ([times [-1] + 30, inlist[2], ">"])
                  else:
                    aggregate_dict [ keyval ].append ([times [-1], inlist[1], ">"])
#                    aggregate_dict [ keyval ].append ([times [-1], inlist[1], inlist[2]])
                elif len (inlist) == 2:
                  aggregate_dict [ keyval ].append ([times [-1], inlist[1]])
#                  aggregate_dict [ keyval ].append ([times [-1] + 30, inlist[1], ">"])
              inline = infile.readline()
        elif (inline[0].isdigit()
            or inline[0] == "+"
            or inline[:3] == "NOW"):  # play line
          if inline[:3] == "NOW":
            inline = inline[3:]
          inlist = inline.split()
          print inlist
          subtimes = inlist[0].split(":")
          if len(subtimes) == 3:
            times.append (3600*int(subtimes[0]) + 60*int(subtimes[1]) + int(subtimes[2]))
          elif len(subtimes) == 2:
            times.append (3600*int(subtimes[0]) + 60*int(subtimes[1]))
          elif len(subtimes) == 1:
            times.append (3600*int(subtimes[0]))
          print times
          if len (inlist) == 3:
            if (inlist [1] == "=="
                or inlist [1] == "<>"
                or inlist [1] == "--"):
              play_list.append ([times [-1], inlist[2]])
              play_list.append ([times [-1] + 30, inlist[2], ">"])
            else:
              play_list.append ([times [-1], inlist[1], ">"])
#              play_list.append ([times [-1], inlist[1], inlist[2]])
          elif len (inlist) == 2:
            play_list.append ([times [-1], inlist[1]])
#            play_list.append ([times [-1] + 30, inlist[1], ">"])
    inline = infile.readline()
  infile.close()
  print sequence_dict
  print play_list
  if len(aggregate_dict) > 0:  # substitute all aggregates with components
    print aggregate_dict
    for jj in xrange (0, len(aggregate_dict)):
      ii = 0
      while ii < len(play_list):
        curline = play_list [ii]
        voicelist = aggregate_dict.get(curline [1])
        if voicelist != None:
          play_list.remove (play_list [ii])
          for voice in voicelist:
            play_list.insert (ii, voice)
            print voice
            ii += 1
        else:
          ii += 1
    print play_list
  if len(play_list) > 0:
    lastline = play_list [0]
    if len(play_list) > 1:
      for ii in xrange (1, len(play_list)):
        curline = play_list [ii]
        #  calculate how long the voice sequence should play
        duration = curline[0] - lastline[0]
        while duration < 0:
          duration += 3600
        hours = duration//3600
        if hours == 0:
          hours = "00:"
        elif hours < 10:
          hours = "0" + str(hours) + ":"
        else:
          hours = str(hours) + ":"
        duration %= 3600
        minutes = duration//60
        if minutes == 0:
          minutes = "00:"
        elif minutes < 10:
          minutes = "0" + str(minutes) + ":"
        else:
          minutes = str(minutes) + ":"
        duration %= 60
        seconds = duration
        if seconds == 0:
          seconds = "00"
        elif seconds < 10:
          seconds = "0" + str(seconds)
        else:
          seconds = str(seconds)
        if ii == 1:
          outline = (hours+minutes+seconds+sep+"<"+"\n")  # write the duration of the voices
        elif ii == len(play_list) - 1:
          outline = (hours+minutes+seconds+sep+">"+"\n")  # write the duration of the voices
        else:
          outline = (hours+minutes+seconds+"\n")  # write the duration of the voices
        outfile.write (outline)
        voicelist = sequence_dict.get(curline [1])
        if voicelist != None:
          for voice in voicelist:
            if (len(curline) > 2
                and curline[2].find(">") != -1
                and voice.find ("binaural") != -1):  # a binaural slide?
              outline = (voice[:-1] + sep + ">" + "\n")
              outfile.write (outline)
            else:  # no slide
              outfile.write (voice)  
        elif (voicelist == None
            and ii == len(play_list) - 1):
          voicelist = sequence_dict.get(lastline [1])
          if voicelist != None:
            for voice in voicelist:
              # no slide
              outfile.write (voice)
        lastline = curline
    else:
      # no way to calculate duration, make 24 hrs
      outfile.write ("24:00:00\n")
      curline = lastline  # only one line
      voicelist = sequence_dict.get(curline [1])
      if voicelist != None:
        for voice in voicelist:
              # no slide
          outfile.write (voice)
  outfile.close()


if __name__ == '__main__':
  convert_sbg_to_discord ()
