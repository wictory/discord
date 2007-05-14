// discord - binaural and chronaural beat generator
// (c) 2007 Stan Lysiak <stanl@cox.net>.  All Rights Reserved.
// For latest version see http://discord.sourceforge.net/.  
// Released under the GNU GPL version 2.  Use at your own risk.
//
// " This program is free software; you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, version 2.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details. "
//
// You should have received a copy of the GNU General Public License
// along with this program; see the file COPYING for details of this license.
// If not, write to the 
// Free Software Foundation, Inc., 
// 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA,
// or visit http://www.fsf.org/licensing/licenses/gpl.html (might change).
//
// The following gpl licensed programs were utilized for discord.
//
// SBaGen - Sequenced Binaural Beat Generator
//
// (c) 1999-2005 Jim Peters <jim@uazu.net>.  All Rights Reserved.
// For latest version see http://sbagen.sf.net/ or
// http://uazu.net/sbagen/.  Released under the GNU GPL version 2.
// Use at your own risk.
//
// " This program is free software; you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, version 2.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details. "
//
// See the file COPYING for details of this license.
//
/*
** libsndfile
** Copyright (C) 1999-2005 Erik de Castro Lopo <erikd@mega-nerd.com>
**
** This program is free software; you can redistribute it and/or modify
** it under the terms of the GNU General Public License as published by
** the Free Software Foundation; either version 2 of the License, or
** (at your option) any later version.
**
** This program is distributed in the hope that it will be useful,
** but WITHOUT ANY WARRANTY; without even the implied warranty of
** MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
** GNU General Public License for more details.
**
** You should have received a copy of the GNU General Public License
** along with this program; if not, write to the Free Software
** Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA.
*/
/*
** libsamplerate
** Copyright (C) 2002-2004 Erik de Castro Lopo <erikd@mega-nerd.com>
**
** This program is free software; you can redistribute it and/or modify
** it under the terms of the GNU General Public License as published by
** the Free Software Foundation; either version 2 of the License, or
** (at your option) any later version.
**
** This program is distributed in the hope that it will be useful,
** but WITHOUT ANY WARRANTY; without even the implied warranty of
** MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
** GNU General Public License for more details.
**
** You should have received a copy of the GNU General Public License
** along with this program; if not, write to the Free Software
** Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA 02111-1307, USA.
*/



#define VERSION "1.0.5"


#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <errno.h>
#include <unistd.h>
#include <ctype.h>
#include <alsa/asoundlib.h>
#include <fcntl.h>
#include <sys/ioctl.h>
#include <sys/time.h>
#include <sys/times.h>
#include <sys/soundcard.h>
#include <samplerate.h>
#include <sndfile.h>
#include <math.h>
#include <stdarg.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <time.h>
#include <getopt.h>
#include <poll.h>
#include <pthread.h>
#include <dlfcn.h>
// typedef long long s64 __uint64_t;

#define SIGNED_SIZEOF(x) ((int) sizeof (x))
#define BUFFER_LEN   (2048)

//typedef sf_count_t int_64 ;
typedef long long int int_64 ;
typedef __uint64_t llong;
typedef unsigned char uchar;

int opt_b;                      // bit accuracy of output
int bit_accuracy = SF_FORMAT_PCM_16;  // bit accuracy of output defaults to 16
int opt_c;                      // Compensate for human hearing low and high freq dropoff
int opt_c_points;               // Number of -c option points provided (max 32)
struct comp_pt
{
  double freq, adj;
}
compensate[32];                 // List of maximum 32 (freq,adj) pairs, freq-increasing order
int opt_d;                      // display sequence only
int opt_e;                      // print status every x seconds
int opt_e_arg = 5;              // store argument to opt_e_arg
int every = 5;                  // default to every five seconds
int opt_f;                      // run fast, at integer multiple of time
int opt_f_arg = 1;              // run fast, at integer multiple of time
int fast_mult = 1;              // default to normal speed
int opt_h;                      // display help
int opt_o;                      // output format to write
int outfile_format = SF_FORMAT_FLAC; // default to flac if not specified otherwise, r:raw, f:flac
int opt_q;                      // quiet run, no display of sequence
int opt_r;                      // samples per second requested
int out_rate = 44100;           // samples per second, default to cd standard
int opt_w;                      // write file instead of sound
char *out_filename;           // write file instead of sound
const char *separators = "='|,;";  // separators for time sequences, mix and match, multiples ok
double *sin_table;
int status_t_retval = 0;  // return integer for status_t thread
int alsa_write_retval = 0;  // return integer for alsa_write thread

#define AMP_DA(pc) (100. * (pc))        // Decimal amplitude to percent
#define AMP_AD(amp) ((amp) / 100.)      // Percent amplitude value to decimal

FILE *infile;                   // Input stream for sound data, or 0
FILE *outfile;                   // Output stream for sound data, or 0

/* node to contain an option and its
   value if required */
typedef struct saved_option saved_option;
struct saved_option
{
  struct saved_option *prev;
  struct saved_option *next;
  char option;
  char *option_string;
} ;

/* string of saved options */
saved_option *SO = NULL;

/* node to contain a time sequence
   line */
typedef struct time_seq time_seq;
struct time_seq
{
  struct time_seq *prev;
  struct time_seq *next;
  char *sequence;
} ;
/* holds a time sequence */
time_seq *TS = NULL;

typedef struct sndstream sndstream;
// the linked list node for a sound to be played
struct sndstream
{
  sndstream *prev;
  sndstream *next;
  int duration;                 // in seconds
  int_64 tot_frames;
  int_64 cur_frames;
  void *voices;
  int fade;  // 0 is no fade, 1 is fade in, 2 is fade out
} ;

// the root node of the play sequence
sndstream *play_seq;

/* structure to set a stub for handling voices */
typedef struct stub stub;
struct stub
{
  void *prev;
  void *next;
  int type;                 // use type to assign to actual voice below
} ;

/* structure to set a binaural beat */
typedef struct binaural binaural;
struct binaural
{
  void *prev;
  void *next;
  int type;                 // 1
  double carrier;               // Carrier freq
  double beat;                  // Resonance freq or beat freq
  double amp;                   // Amplitude level 0-100%, stored as decimal. i.e. .06
  double amp_beat1, amp_beat2;  // Amplitude beat for each channel, frequency of variation
  double amp_pct1, amp_pct2;    // Amplitude adjustment for each channel, per cent band to vary +/- within
  int inc1, off1;               // for binaural tones, offset + increment into sine
  int inc2, off2;               // table for each channel
  int amp_inc1, amp_off1;       // sin table ofset and increment for left amp
  int amp_inc2, amp_off2;       // sin table ofset and increment for right amp
  double carr_adj, beat_adj, amp_adj;   // continuous adjustment if desired
  double amp_beat1_adj, amp_beat2_adj, amp_pct1_adj, amp_pct2_adj;   // continuous adjustment if desired
  int slide;     // 1 if this sequence slides into the next (only binaurals slide)
    /* to avoid discontinuities at the join between voices, use last offset into sin table of previous voice as
        starting offset for this voice.  Store a pointer to it during setup.
    */
  int *last_off1, *last_off2;   
  int first_pass;  // is this voice inactive?
} ;

/* structure for playing a bell during the beat */
typedef struct bell bell;
struct bell
{
  void *prev;
  void *next;
  int type;                 // 2
  double carrier;               // Carrier freq
  double amp;          // Amplitude level 0-100%, stored as decimal
  double split_begin, split_end, split_now;      // left fraction for bell, .5 means evenly split L and R
  double amp_min, amp_max;      // Amplitude min and max for bell tones
  double split_low, split_high; // range for split, .5 means evenly split L and R
  // Min/max time for bell to play, frames, max 0 then min is fixed time.
  int_64 length_min, length_max;
  // Min/max time between bells, max zero then min is fixed period, frames
  int_64 repeat_min, repeat_max;
  /* amplitude behavior of bell,
     1 decrease linearly to 0
     2 decrease linearly to .5, 
     3 constant,
     4 increase linearly to 1.10,
     5 decrease exponentially to 0 */
  int behave;
  int inc1, off1;               // for bell tones, offset + increment into sine
                                // table for each channel
  int_64 next_play, sofar;             // Frames till next bell, how many so far
  int_64 ring;                    // number of frames to ring the bell
  double amp_adj, split_adj;      // adjust while bell is ringing
} ;

/* structure for playing a noise component with beat */
typedef struct noise noise;
struct noise
{
  void *prev;
  void *next;
  int type;                 // 3
  double carrier;               // Carrier freq
  double amp;                   // Amplitude level 0-100%, stored as decimal
  double split_begin, split_end, split_now; // left fraction for noise, .5 means evenly split L and R
  double carrier_min, carrier_max;      // Carrier min and max for noise tones
  double amp_min, amp_max;      // Amplitude min and max for noise tones
  double split_low, split_high; // fraction for noise, random, .5 means evenly split L and R
  // Min/max time for noise to play, frames.
  int_64 length_min, length_max;
  // Min/max time between noises, max zero then min is period, frames
  int_64 repeat_min, repeat_max;
  int behave;                   // amplitude behavior of noise, 1 decrease linearly to 0
  // 2 decrease linearly to .5, 3 constant,
  // 4 increase linearly to 1.10,
  // 5 increase linearly to 1.25
  int behave_low, behave_high;  // range of random amplitude behavior of noise,
  // 1 decrease linearly to .5
  // 2 decrease linearly to .25, 3 constant,
  // 4 increase linearly to 1.25
  // 5 increase linearly to 1.50
  // values the same, then constant
  int inc1, off1;               // for noise tones, offset + increment into sine
  int_64 next_play, sofar;             // Samples till next noise, how many so far
  int_64 play;                    // number of frames to play the noise
  double amp_adj, split_adj;      // adjust while noise is playing
} ;

/* structure for playing a file at random intervals with the beat */
typedef struct stoch stoch;
struct stoch
{
  void *prev;
  void *next;
  int type;                // 4
  short *sound;            // point to buffer of sound, contains whole file, 16 bit sound
  int_64 frames;           // total frames length of sound, 
  int channels;            // number of channels in file, 1 or 2.
  double scale;            // Max amplitude in sound, between 0 and 32767, used to scale output
  double amp;              // Amplitude level 0-100%, stored as decimal i.e. .02
  double amp_min, amp_max;     // Amp level range for sound, begin end chosen randomly unless same.
  double split_begin, split_end, split_now; // left fraction for sound, .5 means evenly split L and R
  double split_low, split_high; // low and high fraction for L sound, .5 means evenly split L and R
  // Min/max frames between random plays
  int_64 repeat_min, repeat_max;
  int_64 next_play, sofar;   // Frames till next play, how many so far
  int_64 off1, play;  //offset into buffer,  number of frames to play, always total frames
  double split_adj; // adjust split while sound is playing
  int mono;  // can be mono sound even with 2 channels.  0:stereo, 1:left mono, 2:right mono
} ;

/* structure for continuously playing file samples with beat */
typedef struct sample sample;
struct sample
{
  void *prev;
  void *next;
  int type;                 // 5
  short *sound;             // point to buffer of sound, contains whole file
  int_64 frames;                 // total frames length of sound, 
  int channels;                 // number of channels in file, 1 or 2.
  double scale;            // Max amplitude in sound, between 0 and 32767, used to scale output
  double amp;                   // Amplitude level 0-100%, stored as decimal i.e. .02
  double amp_min, amp_max;     // Amp level range for sound, begin end chosen randomly unless same.
  double split_begin, split_end, split_now; // left fraction for sound, .5 means evenly split L and R
  double split_low, split_high; // low and high fraction for L sound, .5 means evenly split L and R
  int_64 size, sofar;   // Frames for each sample, how many so far
  int_64 off1, play;   // Position in file for sample, currently playing
  double split_adj; // adjust split while sound is playing
  int mono;  // can be mono sound even with 2 channels.  0:stereo, 1:left mono, 2:right mono
} ;

/* structure for repeat loop of file with beat */
typedef struct repeat repeat;
struct repeat
{
  void *prev;
  void *next;
  int type;                 // 6
  short *sound;             // point to buffer of sound, contains whole file
  int_64 frames;                 // total frames length of sound, 
  int channels;                 // number of channels in file, 1 or 2.
  double scale;            // Max amplitude in sound, between 0 and 32767, used to scale output
  double amp;                   // Amplitude level 0-100%, stored as decimal i.e. .02
  double amp_min, amp_max;     // Amp level range for sound, begin end chosen randomly unless same.
  double split_begin, split_end, split_now; // left fraction for sound, .5 means evenly split L and R
  double split_low, split_high; // low and high fraction for L sound, .5 means evenly split L and R
  int_64 sofar;   // Frames so far, when == frames, wrap
  int_64 off1, play;   // Position in file for sample, currently playing
  double split_adj; // adjust split while sound is playing
  int mono;  // can be mono sound even with 2 channels.  0:stereo, 1:left mono, 2:right mono
} ;

/* structure for playing a file once with the beat */
typedef struct once once;
struct once
{
  void *prev;
  void *next;
  int type;                // 7
  short *sound;            // point to buffer of sound, contains whole file, 16 bit sound
  int_64 frames;           // total frames length of sound, 
  int channels;            // number of channels in file, 1 or 2.
  double scale;            // Max amplitude in sound, between 0 and 32767, used to scale output
  double amp;              // Amplitude level 0-100%, stored as decimal i.e. .02
  double amp_min, amp_max;     // Amp level range for sound, begin end chosen randomly unless same.
  double split_begin, split_end, split_now; // left fraction for sound, .5 means evenly split L and R
  double split_low, split_high; // low and high fraction for L sound, .5 means evenly split L and R
  int_64 play_when;  // when to play the sound, seconds
  int_64 next_play, sofar;   // Frames till next play, how many so far
  int_64 off1, play;  //offset into buffer,  number of frames to play, always total frames
  double split_adj; // adjust split while sound is playing
  int mono;  // can be mono sound even with 2 channels.  0:stereo, 1:left mono, 2:right mono
} ;

/* structure for playing a chronaural beat */
typedef struct chronaural chronaural;
struct chronaural
{
  void *prev;
  void *next;
  int type;                 // 8
  double carrier;               // Carrier freq
  double amp;   // Amplitude level 0-100%, stored as decimal. i.e. .06
  double amp_beat;   // Amplitude variation frequency
  double amp_fraction;   // Fraction of cycle to allow amp beat, actually sin threshold
  int amp_behave;
  /* amplitude behavior of chronaural:
     1 sine wave
     2 square wave
     3 dirac delta approximation
  */
  double split_begin, split_end, split_now;      // left fraction for chronaural, .5 means evenly split L and R
  double split_low, split_high; // range for split, .5 means evenly split L and R
  double split_beat;   // Split variation frequency, defaults to amp_beat
  int slide;     // 1 if this sequence slides into the next (binaurals and chronaurals slide)
  int inc1, off1;               // for chronaural tones, offset + increment into sine table for carrier
  int inc2, off2;               // for chronaural tones, offset + increment into sine table for amp_beat
  double carr_adj, amp_beat_adj, amp_adj, split_beat_adj, split_adj;   // continuous adjustment if desired
    /* to avoid discontinuities at the join between voices, use last offset into sin table of previous voice as
        starting offset for this voice.  Store a pointer to it during setup.
    */
  int *last_off1, *last_off2;   
  int first_pass;  // is this voice inactive?
} ;

/* structure for playing a slice of the output via thread, arguments  to alsa_play_*  and file_write */
typedef struct slice slice;
struct slice
{
  snd_pcm_t *alsa_dev;  // pointer to the alsa device playing the slice 
  SNDFILE *sndfile;  // pointer to the file device writing the slice 
  double *buffer;  // pointer to the buffer to be played;  void makes it flexible
  int frames;  // number of frames in the buffer
  int channels;  // number of channels in a frame
} ;
/* mutexes for the alsa_play thread, allow maximum utilization of cpu */
pthread_mutex_t mtx_play = PTHREAD_MUTEX_INITIALIZER;  // mutex for play thread
pthread_mutex_t mtx_write = PTHREAD_MUTEX_INITIALIZER;  // mutex for write thread

/* structure for displaying a point in time of the current sound stream, arguments to status */
typedef struct point_in_time point_in_time;
struct point_in_time
{
  sndstream *snd1;  // pointer to the current sound stream
  //void *voice;  // pointer to the first voice of the current sound stream
  FILE *fp;  // pointer to the device on which to display (can be file)
} ;
/* mutexe for the status thread, allow maximum utilization of cpu */
pthread_mutex_t mtx_status = PTHREAD_MUTEX_INITIALIZER; // mutex for status thread

int main (int argc, char **argv);
void init_sin_table ();
void debug (char *fmt, ...);
void warn (char *fmt, ...);
void *Alloc (size_t len);
char *StrDup (char *str);
double amp_comp (double freq);
void error (char *fmt, ...);
int read_time (char *, int *);
void help ();
int parse_argv_options (int argc, char **argv);
int parse_argv_configs (int argc, char **argv);
int set_options ();
int setup_play_seq ();
int read_file (FILE * infile, char **config_options);
int append_options (char *config_options);
int setup_opt_c (char *spec);
void setup_binaural (char *token, void **work);
void setup_bell (char *token, void **work);
int setup_noise (char *token, void **work);
void setup_stoch (char *token, void **work);
void setup_sample (char *token, void **work);
void setup_repeat (char *token, void **work);
void setup_once (char *token, void **work);
void setup_chronaural (char *token, void **work);
void init_binaural ();
void play_loop ();
void save_loop ();
int generate_frames (struct sndstream *snd1, double *out_buffer, int at_offset, int frame_count);
inline double round (double num);
void status (sndstream * snd1, FILE * fp);
void *status_t (void *call_parms); // version for threading
void sprintTime (char **p);
int fprint_time (FILE *fp);
void sprintVoiceAll (char **p, void *this);
int fprint_voice_all (FILE *fp, void *this);
void sprintVoice (char **p, void *this);
int fprint_voice (FILE *fp, void *this);
static snd_pcm_t *alsa_open (snd_pcm_t *alsa_dev, int channels, unsigned samplerate, int realtime);
//static int alsa_write_int32 (snd_pcm_t *alsa_dev, int *data, int frames, int channels);
static int alsa_write_double (snd_pcm_t *alsa_dev, double *data, int frames, int channels) ;
void *alsa_write (void *call_parms); // version for threading
static sf_count_t sample_rate_convert (SNDFILE *infile, SNDFILE *outfile, int converter, 
                                        double src_ratio, int channels, double * gain) ;
static double apply_gain (float * data, long frames, int channels, double max, double gain) ;
long check_samplerate (char *inname);

//extern int out_rate, out_rate_def;
extern char *optarg;            // for getopt_long
extern int optind, opterr, optopt;      // for getopt

#define ALLOC_ARR(cnt, type) ((type*)Alloc((cnt) * sizeof(type)))
#define uint unsigned int

#define NL "\n"

void
usage ()
{
  error ("discord - Create and mix binaural and chronaural beats, version " VERSION NL
         "Copyright (c) 2007 Stan Lysiak, all rights " NL
         "  reserved, released under the GNU GPL v2.  See file COPYING." NL NL
         "Usage: discord [options] seq-file ..." NL NL
         "For full usage help, type 'discord -h'.  For latest version see" NL
         "http://discord.sourceforge.net/"
         NL);
}

char buf[32768];                 // Buffer for space holder
// START OF PROGRAMS
//
// M A I N
//

int
main (int argc, char **argv)
{
  time_t time_now, utc_secs;

  // argc--;  // remove program name if necessary
  // argv++;
  time_now = time(&utc_secs);  // seconds since Jan 1 1970 UTC
  srand48(time_now);  // initialize the drand48 generator
  parse_argv_options (argc, argv);  // parse command line options
  parse_argv_configs (argc, argv); // parse configuration files
  set_options ();  // set the options now that complete
  init_sin_table ();  // now that rate is known, create lookup sin table
  setup_play_seq ();  // set the voices now that options complete
  if (opt_w)  // write a file
    save_loop ();  // save the sequences to a file until done
  else
    play_loop ();  // play the sequences until done using buffer output
  return 0;
}

int
read_time (char *p, int *timp)
{                               // Rets chars consumed, or 0 error
  int nn = 0, hh, mm, ss;
  char *token, *empty = NULL, **endptr = NULL;

  token = strtok (p, ":");
  if (token)
  {
    hh = (int) strtol (token, endptr, 10);
    token = strtok (empty, ":");
    if (token)
    {
      nn += 3;                  // hours chars
      endptr = NULL;
      mm = (int) strtol (token, endptr, 10);
      empty = NULL;
      token = strtok (empty, ":");
      if (token)
      {
        nn += 5;                // min + sec chars
        endptr = NULL;
        ss = (int) strtol (token, endptr, 10);
      }
      else
      {
        nn += 2;                // min chars
        ss = 0;
      }
    }
    else
    {
      nn += 2;                  // hours chars
      mm = ss = 0;
    }
  }
  else
    hh = mm = ss = 0;
  if (hh < 0 || hh >= 24 || mm < 0 || mm >= 60 || ss < 0 || ss >= 60)
    return 0;
  else
    *timp = ( (hh * 60 + mm) * 60 + ss);
  return nn;
}

/* parses options using getopt_long
   and places them in a linked list */
int
parse_argv_options (int argc, char **argv)
{
  const char *ostr = "b:c:de:f:ho:qr:w:";
  int c;
  int option_index = 0;
  saved_option *soh = NULL, *sow = NULL;
  static struct option long_options[] =
    {
      {"bit_accuracy", 1, 0, 'b'},
      {"compensate", 1, 0, 'c'},
      {"display_only", 0, 0, 'd'},
      {"every", 1, 0, 'e'},
      {"fast", 1, 0, 'f'},
      {"help", 0, 0, 'h'},
      {"out_format", 1, 0, 'o'},
      {"quiet", 0, 0, 'q'},
      {"rate", 1, 0, 'r'},
      {"write", 1, 0, 'w'},
      {0, 0, 0, 0}
    };

  while (1)
  {
    c = getopt_long (argc, argv, ostr, long_options, &option_index);
    if (c == -1)
      break;
    switch (c)
    {
      case 0:
        fprintf (stderr, "%s\n", "Error in long option struct, return was a 0");
        fflush (stderr);
        break;

      case ':':
        //free_all_alloc ();          // free memory
        error ("Option \"-%c\" or \"--%s\" requires an argument", (char) c,
               long_options[option_index].name);
        break;

      case 'b':
      case 'c':
      case 'd':
      case 'e':
      case 'f':
      case 'h':
      case 'o':
      case 'q':
      case 'r':
      case 'w':
        soh = (saved_option *) Alloc ((sizeof (saved_option)) * 1);
        soh->next = NULL;
        if (SO == NULL)         // option list doesn't exist
        {
          soh->prev = NULL;
          SO = soh;
        }
        else
        {
          soh->prev = sow;
          sow->next = soh;
        }
        sow = soh;
        sow->option = (char) c;         // option
        if (optarg != NULL)     // has argument
          sow->option_string = StrDup (optarg);
        else
          sow->option_string = NULL;
        break;

      case '?':
        fprintf (stderr, "%s\n", "Option not found in long option struct");
        fflush (stderr);
        break;

      default:
        printf ("?? getopt returned character code 0%o ??\n", c);
    }
  }
  return optind;                // index into argv where non options start i.e. filenames
}

/* parses the configuration files for
   options and time sequences.  Places
   them in appropriate linked lists.
   The time sequences can't be processed
   until all of the options have been
   determined. */
int
parse_argv_configs (int argc, char **argv)
{
  char *filename;
  int filecount = 0;
  FILE *infile;
  // points to a string containing all the configuration file options
  char *config_options = NULL;

  if (optind < argc) // optind is global var set by getopts_long
  {
    while (optind < argc)
    {
      filecount++;
      filename = argv[optind++];
      infile = fopen (filename, "r");
      read_file (infile, &config_options);
      append_options (config_options);
      fclose (infile);
    }
  }
  return filecount;             // count of configuration files
}

/*  Process a string of options from
    a config file.  Append them to
    SO, the linked list of options
    from the command line, if it exists.
    Create it if it doesn't. */
int
append_options (char *config_options)
{
  const char *ostr = "b:c:de:f:ho:qr:w:";
  char *found;
  char *token, *subtoken;
  char *str1, *str2;
  char *saveptr1, *saveptr2;
  int tlen;
  saved_option *soh = NULL, *sow = NULL;
  static struct option long_options[] =
    {
      {"bit_accuracy", 1, 0, 'b'},
      {"compensate", 1, 0, 'c'},
      {"display_only", 0, 0, 'd'},
      {"every", 1, 0, 'e'},
      {"fast", 1, 0, 'f'},
      {"help", 0, 0, 'h'},
      {"out_format", 1, 0, 'o'},
      {"quiet", 0, 0, 'q'},
      {"rate", 1, 0, 'r'},
      {"write", 1, 0, 'w'},
      {0, 0, 0, 0}
    };

  str1 = config_options;
  token = strtok_r (str1, " \t\n", &saveptr1);          // get first token after spaces or tabs
  str1 = NULL;
  while (token != NULL)
  {
    soh = (saved_option *) Alloc ((sizeof (saved_option)) * 1);
    soh->next = NULL;
    if (SO == NULL)             // option list doesn't exist, no command line options
    {
      soh->prev = NULL;
      SO = soh;
    }
    else
    {
      if (sow == NULL)  // first time through, there are command line options
      {
        sow = SO;  // start at root of linked list of options
        while (sow->next != NULL)
            sow = sow->next;
      }
      soh->prev = sow;
      sow->next = soh;
    }
    sow = soh;
    while (*token == '-')       // allows long options with single leading -
      token++;
    tlen = strlen (token);
    if (tlen > 1) // long option, short option with arg, or multiple short options
    {
      str2 = token;
      subtoken = strtok_r (str2, "=", &saveptr2);       // if arg assigned, remove
      str2 = NULL;
      int long_idx = 0;

      while (long_options[long_idx].name != NULL)       // look for long option
      {
        if (strcasecmp (long_options[long_idx].name, subtoken) == 0)
        {
          if (long_options[long_idx].has_arg == 1)      // has argument
          {
            sow->option = long_options[long_idx].val;    // assign short option
            subtoken = strtok_r (str2, "=", &saveptr2);
            if (subtoken != NULL)       // = form of arg assignment
              sow->option_string = StrDup (subtoken);
            else                // get next token after spaces or tabs
            {
              token = strtok_r (str1, " \t\n", &saveptr1);
              sow->option_string = StrDup (token);
            }
          }
          else                  // no argument
            sow->option_string = NULL;
          break;
        }
        long_idx++;
      }
      if (long_options[long_idx].name == NULL) // not a long option, hit end of list
      {
        if ( (found = strchr (ostr, (int) token[0])) != NULL)           // short option?
        {
          if (found[1] != ':')          // has no argument, must be multiple short options
          {
            sow->option = token[0];
            sow->option_string = NULL;
            token++;            // next option
            tlen--;             // shorten token string
            while (tlen > 0)    // rest of short options
            {
              // legitimate short option?
              if ( (found = strchr (ostr, (int) token[0])) != NULL)
              {
                // just found another option above, can't be first
                soh = (saved_option *) Alloc ((sizeof (saved_option)) * 1);
                soh->prev = sow;
                soh->next = NULL;
                sow->next = soh;
                sow = soh;
                sow->option = token[0];
                if (found[1] != ':')    // has no argument
                {
                  sow->option_string = NULL;
                  token++;      // next option
                  tlen--;       // shorten token string
                }
                else if (tlen > 1)      // should have argument
                {
                  sow->option_string = StrDup (token + 1);      // rest of string is argument
                  tlen = 0;
                }
                else            // next token is argument, tlen == 1
                {
                  token = strtok_r (str1, " \t\n", &saveptr1);          // get next token after spaces or tabs
                  if (token != NULL && token[0] != '-')
                  {
                    sow->option_string = StrDup (token);        // token is argument
                    tlen = 0;
                  }
                  else          // missing argument
                  {
                    free (sow);
                    error ("Option %c requires an argument, not provided.\n", found[0]);
                  }
                }
              }
              else
              {
                free (sow);
                error("Option %c is not legitimate.\n", token[0]);
              }
            }
          }
          else                // should have argument
            sow->option_string = StrDup (token + 1);    // rest of string is argument
        }
        else
        {
          free (sow);
          error("Option %c is not legitimate.\n", token[0]);
        }
      }
    }
    else if (tlen == 1)       // single character, has to be short option
    {
      if ( (found = strchr (ostr, (int) token[0])) != NULL)
      {
        sow->option = token[0];
        if (found[1] != ':')          // no argument
        {
          sow->option_string = NULL;
        }
        else                  // should have argument
        {
          // get next token after spaces or tabs
          token = strtok_r (str1, " \t\n", &saveptr1);
          if (token != NULL)
            sow->option_string = StrDup (token);
          else
          {
            free (sow);
            error ("Option %c requires an argument, not provided.\n", sow->option);
          }
        }
      }
      else
      {
        free (sow);
        error("Option %c is not legitimate.\n", token[0]);
      }
    }
    token = strtok_r (str1, " \t\n", &saveptr1);      // get next token after spaces or tabs
  }
  return 0;                   // successful exit
}

/*
   Read a configuration/sequence file, discarding blank
   lines and comments.  Rets: 0 on success.
   Everything from the file is put into a character
   string for options, or a linked list for play sequences. */

int
read_file (FILE * infile, char **config_options)
{
  char *curlin, *cmnt, *token;
  char savelin[4096], worklin[4096], rawline[4096];
  size_t len, destlen;
  int line_count = 0;
  time_seq *tsh = NULL, *tsw = NULL;

  memset (savelin, 0x00, 4096);
  memset (worklin, 0x00, 4096);
  fgets (worklin, sizeof (worklin), infile);
  strncpy (rawline, worklin, 4096); // strtok is destructive, save raw copy of line
  curlin = rawline;
  while (*curlin != '\0')
  {
    line_count++;
    token = strtok (worklin, " \t\n");    // get first token after spaces or tabs
    if (token)                  // not an empty line
    {
      cmnt = strchr (curlin, '#');
      if (cmnt && cmnt[1] == '#')
      {
        fprintf (stderr, "Configuration comment  %s\n", curlin);
        fflush (stderr);
      }
      if (token[0] == '-')      // options line
      {
        if (cmnt)
          strncpy (cmnt, " \0", 2);     // truncate at comment
        while (isspace (*curlin))       // remove leading spaces
          curlin++;
        len = strlen (curlin);
        destlen = strlen (savelin);
        if (destlen == 0)  // no options saved yet
          strncpy (savelin, curlin, len);
        else
        {
          if (savelin[0] == '-')  // already some options saved
            strncat (savelin, curlin, len);
          else
            error ("Options are only permitted at start of sequence file:\n  %s", curlin);
        }
      }
      else if (isdigit (token[0]) && strchr (token, ':') != NULL) // start of a time sequence
      {
        if (savelin[0] == '-')          // just finished the options
        {
          *config_options = StrDup (savelin);    // save them for further processing
          memset (savelin, 0x00, 4096);         // reset saved line
        }
        else if (strchr(savelin, ':') != NULL)   // just finished a time sequence
        {
          tsh = (time_seq *) Alloc (sizeof (time_seq) * 1);      // allocate struct for it
          tsh->next = NULL;
          if (TS == NULL)       // time seq list doesn't exist
          {
            tsh->prev = NULL;
            TS = tsh;
          }
          else
          {
            tsh->prev = tsw;
            tsw->next = tsh;
          }
          tsw = tsh;
          tsw->sequence = StrDup (savelin);        // save them
          memset (savelin, 0x00, 4096);         // reset saved line
        }
        if (cmnt)
          strncpy (cmnt, " \0", 2);     // truncate at comment, add trailing space
        while (isspace (*curlin))       // remove leading spaces, not really necessary
          curlin++;
        len = strlen (curlin);
        strncpy (savelin, curlin, len);  // here only at start of time sequence
      }
      else if (isalpha (token[0]))    // a sequence continuation, can't split voice
      {
        if (cmnt)
          strncpy (cmnt, " \0", 2);     // truncate at comment, add trailing space
        destlen = strlen (savelin);
        len = strlen (curlin);
        if (destlen == 0)
        {
          strncpy (savelin, curlin, len);
        }
        else if (destlen + len + 1 < 4096)
        {
          strncat (savelin, " ", 1);  // add trailing space so voices are separate
          strncat (savelin, curlin, len);  // add voices
        }
        else
          error ("Too many voices to store in seqence %s", savelin);
      }
      else if (token[0] == '#') // line is a comment
        ;  // do nothing
      else
        fprintf (stderr, "Skipped line with token %s at start of line\n", token);
    }
    memset (worklin, 0x00, 4096);
    fgets (worklin, sizeof (worklin), infile);
    strncpy (rawline, worklin, 4096); // strtok is destructive, save raw copy of line
    curlin = rawline;
  }
  if (*curlin == '\0')
  {
    if (feof (infile))
    {                           // save last time sequence
      tsh = (time_seq *) Alloc ((sizeof (time_seq)) * 1);
      tsh->next = NULL;
      if (TS == NULL)           // time seq list doesn't exist
      {
        tsh->prev = NULL;
        TS = tsh;
      }
      else
      {
        tsh->prev = tsw;
        tsw->next = tsh;
      }
      tsw = tsh;
      tsw->sequence = StrDup (savelin);        // save them
      return 0;
    }
    error ("Read error on sequence file");
  }
  return 0;
}

/*  Process the linked list of options
    pointed to by global SO.  Do it in reverse
    so that later options are overridden
    by earlier options. */
int
set_options ()
{
  char *endptr;
  int c;
  saved_option *sow;

  if (SO == NULL)               // option list doesn't exist
    return 0;                   // successful :-)
  sow = SO;
  while (sow->next != NULL)     // move to end
    sow = sow->next;
  while (sow != NULL)
  {
    c = sow->option;
    switch (c)
    {
      case 'b':  // bit accuracy of sound generated, 16i, 24i, 32i, 32f, 64f
        opt_b = 1;
        if (strcmp(sow->option_string, "16i") == 0)
          bit_accuracy = SF_FORMAT_PCM_16;
        else if (strcmp(sow->option_string, "24i") == 0)
          bit_accuracy = SF_FORMAT_PCM_24;
        else if (strcmp(sow->option_string, "32i") == 0)
          bit_accuracy = SF_FORMAT_PCM_32;
        else if (strcmp(sow->option_string, "32f") == 0)
          bit_accuracy = SF_FORMAT_FLOAT;
        else if (strcmp(sow->option_string, "64f") == 0)
          bit_accuracy = SF_FORMAT_DOUBLE;
        else // default to 16 bit sound
          fprintf (stderr, "Unrecognized format for --bit_accuracy/-b %s.  Setting to 16 bit.\n", sow->option_string);
          bit_accuracy = SF_FORMAT_PCM_16;
        break;
      case 'c':  // compensate for human hearing, lower freqs need to be louder
        opt_c = 1;
        opt_c_points = setup_opt_c (sow->option_string);
        fprintf (stderr, "opt_c_points %d\n", opt_c_points);
        break;
      case 'd':  // display only
        opt_d = 1;
        break;
      case 'e':  // every, display status every x seconds
        opt_e = 1;
        errno = 0;
        opt_e_arg = strtod (sow->option_string, &endptr);
        if (opt_e_arg == 0.0)
        {
          if (errno == 0)       // no errors
          {
            fprintf (stderr, "Seconds for --every/-e cannot be 0.  Setting to 5.\n");
            every = 5;
          }
          else                  // there was an error
            error ("--every/-e expects numeric seconds");
        }
        else
          every = (int) fabs (opt_e_arg);
        break;
      case 'f':  // fast, move through at multiple of time
        opt_f = 1;
        errno = 0;
        opt_f_arg = strtod (sow->option_string, &endptr);
        if (opt_f_arg == 0.0)
        {
          if (errno == 0)       // no errors
          {
            fprintf (stderr, "Multiplier for --fast/-f cannot be 0.  Setting to 1.\n");
            fast_mult = 1;
          }
          else                  // there was an error
            error ("--fast/-f expects numeric multiplier");
        }
        else
          fast_mult = (int) fabs (opt_f_arg);
        break;
      case 'h':  // help
        help ();
        break;
      case 'o':  // output file format
        opt_o = 1;
        if (sow->option_string != NULL)
        {
          if (sow->option_string[0] == 'f')
            outfile_format = SF_FORMAT_FLAC;
          else if (sow->option_string[0] == 'r')
            outfile_format = SF_FORMAT_RAW;
          else if (sow->option_string[0] == 'w')
            outfile_format = SF_FORMAT_WAV;
          else  // default to flac
            fprintf (stderr, "Unrecognized format for --output/-o %c.  Setting to flac.\n", sow->option_string[0]);
            outfile_format = SF_FORMAT_FLAC;
        }
        else  // default to flac
          outfile_format = SF_FORMAT_FLAC;
        break;
      case 'q':                // quiet
        opt_q = 1;
        break;
      case 'r':  // frame rate per second
        opt_r = 1;
        errno = 0;
        out_rate = (int) strtol (sow->option_string, (char **) NULL, 10);
        if (errno != 0)
          error ("Expecting an integer after --rate/-r");
        break;
      case 'w':  // write to file
        opt_w = 1;
        if (sow->option_string != NULL)
          out_filename = StrDup(sow->option_string);
        else  // default to generic name
          out_filename = "discord_save_file.flac";
        break;
      default:
        error ("Option -%c not known; run 'discord -h' for help", c);
    }
    sow = sow->prev;
  }
  return 0;                     // success
}

//
// Setup the compensate[] array from the given --compensate/-c spec-string
//

int
setup_opt_c (char *config)
{
  char *token, *freq, *comp;
  char *str1, *str2;
  char *saveptr1, *saveptr2;
  char *endptr;
  int max_points;
  int point_count = 0;

  max_points = sizeof (compensate) / sizeof (compensate[0]);
  str1 = config;
  token = strtok_r (str1, ",'", &saveptr1);          // get first token after commas or apostrophes
  str1 = NULL;
  while (token != NULL)
  {
    if (point_count >= max_points)
      error ("Too many -c option frequencies; maxmimum is %d", max_points);
    str2 = token;
    freq = strtok_r (str2, "=:", &saveptr2);       // get frequency separated by = or :
    str2 = NULL;
    comp = strtok_r (str2, "=:", &saveptr2);       // get compensation
    errno = 0;
    double holder = strtod (freq, &endptr);
    if (holder <= 0.0)
    {
      if (errno == 0)             // no errors
        error ("Bad --compensate/-c option spec zero or less; %s %s", freq, comp);
      else                        // there was an error
        error ("Bad --compensate/-c option spec invalid; %s %s", freq, comp);
    }
    compensate[point_count].freq = holder;
    errno = 0;
    holder = strtod (comp, &endptr);
    if (holder <= 0.0)
    {
      if (errno == 0)             // no errors
        error ("Bad --compensate/-c option spec zero or less; %s %s", freq, comp);
      else                        // there was an error
        error ("Bad --compensate/-c option spec invalid; %s %s", freq, comp);
    }
    compensate[point_count].adj = holder;
    token = strtok_r (str1, ",'", &saveptr1);          // get next token after commas or apostrophes
    point_count++;
  }
  // Sort the list
  int a, b;
  double holder;

  for (a = 0; a < point_count; a++)
    for (b = a + 1; b < point_count; b++)
      if (compensate[a].freq > compensate[b].freq)
      {
        holder = compensate[a].freq;
        compensate[a].freq = compensate[b].freq;
        compensate[b].freq = holder;
        holder = compensate[a].adj;
        compensate[a].adj = compensate[b].adj;
        compensate[b].adj = holder;
      }
  for (a = 0; a < point_count; a++)
    fprintf (stderr, "compensate freq %f comp %f\n",
                compensate[a].freq, compensate[a].adj);
  // Check for duplicate frequencies
  for (a = 0; a < point_count; a++)
    for (b = a + 1; b < a + 2; b++)
      if (compensate[a].freq == compensate[b].freq)
      {
        error ("Bad --compensate/-c option spec multiple of same freq; %f %f", 
                compensate[a].freq, compensate[b].freq);
      }
  return point_count;
}

//
// Calculate amplitude adjustment factor for frequency 'freq'.
// The adjustments are from low freq to high freq in the array.
// One indicates no adj, <1 is attenuation, >1 is amplification.
// Binary search
//

double
amp_comp (double freq)
{
  int point, adjust;
  struct comp_pt *p0, *p1;

  if (!opt_c)
    return 1.0;
  if (freq <= compensate[0].freq)
    return compensate[0].adj;
  if (freq >= compensate[opt_c_points - 1].freq)
    return compensate[opt_c_points - 1].adj;
  point = opt_c_points / 2;  // begin near middle
  adjust = point / 2;  // begin near middle
  while (1)  // binary search
  {
    if (compensate[point].freq > freq)
      point = point - adjust;
    else  // if (compensate[point].freq <= freq)
    {
      if (compensate[point+1].freq > freq)
        break;  // solution!
      else
        point = point + adjust;
    }
    adjust /= 2;  // halve the adjustment
    if (adjust == 0)
      adjust = 1;  // odd number worst case, step by one again
  }
  p0 = &compensate [point];
  p1 = &compensate [point + 1];
  // linear interpolation between points
  return p0->adj + ((p1->adj - p0->adj) * (freq - p0->freq)) / (p1->freq - p0->freq);
}

void
help ()
{
  printf ("dischord - Create mental dischordancy, version " VERSION NL
          "Copyright (c) 2007 Stan Lysiak, all rights " NL
          "  reserved, released under the GNU GPL v2.  See file COPYING." NL NL
          "Derived from sbagen" NL
          "Copyright (c) 1999-2005 Jim Peters, http://uazu.net/, all rights " NL
          "  reserved, released under the GNU GPL v2.  See file COPYING." NL NL
          "Using libsndfile" NL
          "Copyright (C) 1999-2005 Erik de Castro Lopo <erikd@mega-nerd.com>"NL
          "** This program is free software; you can redistribute it and/or modify"NL
          "** it under the terms of the GNU Lesser General Public License as published by"NL
          "** the Free Software Foundation; either version 2.1 of the License, or"NL
          "** (at your option) any later version."NL
          "This program is distributed in the hope that it will be useful,"NL
          "but WITHOUT ANY WARRANTY; without even the implied warranty of"NL
          "MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the"NL
          "GNU General Public License for more details."NL
          "You should have received a copy of the GNU General Public License"NL
          "along with this program; if not, write to the Free Software"NL
          "Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA."NL

          "Usage: dischord [options] seq-file ..." NL NL
          "Options:  -h --help         Display this help-text" NL
          "          -b --bit_accuracy Number of bits to use to represent each sound: integer or float"NL
          "          -c --compensate   Compensate for human hearing perceptual differences: see docs"NL
          "          -d --display      Display the full interpreted sequence instead of playing it"NL
          "          -e --every        Show a status line every x seconds while playing"NL
          "          -f --fast         Fast.  Run through quickly (real time x 'mult')"NL
          "                              rather than wait for real time to pass"NL
          "          -o --outfile      Output raw data to the given file instead of playing"NL
          "          -q --quiet        Don't display running status"NL
          "          -r --rate         Select the output rate (default is 44100 Hz, or from -m)"NL
          "          -w --write        Output a format file instead of raw data"NL);
  exit (0);
}

/* create the lookup table of sin values, double the sample rate */

void
init_sin_table ()
{
  int a;
  int sin_siz = (2 * out_rate);
  double delta, radians;
  double *arr = (double *) Alloc (sin_siz * sizeof (double));

  delta = (2 * 3.1415926535897932384626) / sin_siz;
  radians = 0.0;
  for (a = 0; a < sin_siz; a++)
  {
    arr[a] = (double) sin (radians);
    radians += delta;
  }
  sin_table = arr;
}

/* Set up the sequence of voices that will play */

int
setup_play_seq ()
{
  char *token, *subtoken;
  char voice[256];
  char *str1 = NULL, *str2 = NULL;
  char *saveptr1 = NULL, *saveptr2 = NULL;
  int time_in_secs, len;
  time_seq *tsw = NULL;
  stub *stub1 = NULL, *stub2 = NULL;
  sndstream *sndstream1 = NULL, *sndstream2 = NULL;
  void *work = NULL, *prev = NULL;


  sndstream2 = (sndstream *) Alloc ((sizeof (sndstream)) * 1);
  sndstream2->prev = NULL;
  sndstream2->next = NULL;
  sndstream2->voices = NULL;
  sndstream1 = sndstream2;
  if (play_seq == NULL)
    play_seq = sndstream1;
  tsw = TS;
  while (tsw != NULL)           // move through time sequence linked list
  {
    str1 = tsw->sequence;
    token = strtok_r (str1, " \t\n", &saveptr1);        // get first token after spaces or tabs
    str2 = token;
    subtoken = strtok_r (str2, separators, &saveptr2);    // get subtoken of token, time indicator
    read_time (subtoken, &time_in_secs);
    sndstream1->duration = time_in_secs;
    sndstream1->tot_frames = (int_64) (time_in_secs * out_rate);            // samples for this stream
    sndstream1->cur_frames = (int_64) (0);          // samples so far for this stream
    str2 = NULL;
    subtoken = strtok_r (str2, separators, &saveptr2);    // get next subtoken of token, fade indicator
    if (subtoken == NULL)  // no fade indicator
      sndstream1->fade = 0;  // no fade
    else if (strcmp(subtoken, "<") == 0)
      sndstream1->fade = 1;  // fade in
    else if (strcmp(subtoken, ">") == 0)
      sndstream1->fade = 2;  // fade out
    else  // default is no fade
      sndstream1->fade = 0;
    str1 = NULL;
    token = strtok_r (str1, " \t\n", &saveptr1);        // get next token
    while (token != NULL)
    {
      str2 = token;
      subtoken = strtok_r (str2, separators, &saveptr2);    // get subtoken of token
      str2 = NULL;
      memset (voice, 0x00, 256);
      len = strlen (subtoken);
      strncpy (voice, subtoken, len);  // recreate the voice for setup as token = subtoken
      strncat (voice, "''", 2);  // replace separator
      len = strlen (saveptr2);
      strncat (voice, saveptr2, len);
      if (strcasecmp (subtoken, "binaural") == 0)
        setup_binaural (voice, &work);
      else if (strcasecmp (subtoken, "bell") == 0)
        setup_bell (voice, &work);
      else if (strcasecmp (subtoken, "noise") == 0)
      {
        char voice_save[256];
        memset (voice_save, 0x00, 256);
        strncpy (voice_save, voice, 256);  // save the voice characteristics for reuse
        int many = setup_noise (voice, &work);     // returns a multiple count for this voice
        if (many > 1)  // more than one requested
        {
          many--;
          while (many-- > 0)  // loop will leave last voice for regular logic below
          {
            if (sndstream1->voices == NULL)   // first sequence
            {
              sndstream1->voices = work;  // first voice
              stub2 = (stub *) work;  // interpret as stub (smallest)
              stub2->prev = NULL;  // set the reverse link to NULL, first in chain
              stub2->next = NULL;  // set the forward link for this voice
            }
            else
            {
              stub1 = (stub *) prev;  // interpret as stub (smallest)
              stub1->next = work;  // set the forward link for previous voice
              stub2 = (stub *) work;  // interpret as stub (smallest)
              stub2->prev = prev;  // set the reverse link for this voice
              stub2->next = NULL;  // set the forward link for this voice
            }
            prev = work;  // point to new voice as previous voice
            strncpy (voice, voice_save, 256);  // restore voice characteristics
            setup_noise (voice, &work);  // create another copy of the voice
          }
        }
      }
      else if (strcasecmp (subtoken, "stoch") == 0)
        setup_stoch (voice, &work);
      else if (strcasecmp (subtoken, "sample") == 0)
        setup_sample (voice, &work);
      else if (strcasecmp (subtoken, "repeat") == 0)
        setup_repeat (voice, &work);
      else if (strcasecmp (subtoken, "once") == 0)
        setup_once (voice, &work);
      else if (strcasecmp (subtoken, "chronaural") == 0)
        setup_chronaural (voice, &work);
      else
        error ("Unrecognized time sequence type: %s\n", subtoken);
      /* Append this voice to the rest of the voices for the period/ time sequence */
      if (sndstream1->voices == NULL)   // first sequence
      {
        sndstream1->voices = work;  // first voice
        stub2 = (stub *) work;  // interpret as stub (smallest)
        stub2->prev = NULL;  // set the reverse link to NULL, first in chain
        stub2->next = NULL;  // set the forward link for this voice
      }
      else
      {
        stub1 = (stub *) prev;  // interpret as stub (smallest)
        stub1->next = work;  // set the forward link for previous voice
        stub2 = (stub *) work;  // interpret as stub (smallest)
        stub2->prev = prev;  // set the reverse link for this voice
        stub2->next = NULL;  // set the forward link for this voice
      }
      prev = work;  // point to new voice as previous voice
      token = strtok_r (str1, " \t\n", &saveptr1);      // get next token
    }
    tsw = tsw->next;  // get next period, time sequence
    if (tsw != NULL)
    {
      sndstream2 = (sndstream *) Alloc ((sizeof (sndstream)) * 1);
      sndstream2->prev = sndstream1;
      sndstream2->next = NULL;
      sndstream2->voices = NULL;
      sndstream1->next = sndstream2;
      sndstream1 = sndstream2;
    }
  }
  init_binaural ();  // complete binaural and chronaural setup now that sequences are known
  return 0;
}

/* Set up a binaural sequence */

void
setup_binaural (char *token, void **work)
{
  char *endptr;
  char *subtoken;
  char *str2 = NULL;
  char *saveptr2;
  binaural *binaural1 = NULL;

  binaural1 = (binaural *) Alloc ((sizeof (binaural)) * 1);
  *work = (void *) binaural1;
  binaural1->next = NULL;
  binaural1->type = 1;
  binaural1->slide = 0;  // default to not slide
  binaural1->off1 = binaural1->off2 = 0;  // begin at 0 degrees
  binaural1->last_off1 = binaural1->last_off2 = NULL;  // no previous voice offsets yet
  binaural1->first_pass = 1;  // inactive
  str2 = token;

  subtoken = strtok_r (str2, separators, &saveptr2);        // remove voice type
  str2 = NULL;
  
  subtoken = strtok_r (str2, separators, &saveptr2);        // get subtoken of token
  errno = 0;
  double carrier = strtod (subtoken, &endptr);
  if (carrier == 0.0)
  {
    if (errno == 0)             // no errors
      error ("Carrier for binaural cannot be 0.\n");
    else                        // there was an error
      error ("Carrier for binaural had an error.\n");
  }
  binaural1->carrier = carrier;

  subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
  errno = 0;
  double beat = strtod (subtoken, &endptr);
  if (beat == 0.0)
  {
    if (errno != 0)             //  error
      error ("Beat for binaural had an error.\n");
  }
  binaural1->beat = beat;

  subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
  errno = 0;
  double amp = strtod (subtoken, &endptr);
  if (amp == 0.0)
  {
    if (errno != 0)             //  error
      error ("Amplitude for binaural had an error.\n");
  }
  binaural1->amp = AMP_AD(amp);

  subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
  if (subtoken != NULL && strcmp (subtoken, ">") == 0)  // there and slide, done, no amp variation
    binaural1->slide = 1;
  else if (subtoken != NULL)  // there, not slide, must be amp variation
  {
    errno = 0;
    double amp_beat1 = strtod (subtoken, &endptr);
    if (amp_beat1 == 0.0)
    {
      if (errno != 0)             //  error
        error ("Amplitude beat1 for binaural had an error.\n");
    }
    binaural1->amp_beat1 = amp_beat1;

    subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
    errno = 0;
    double amp_beat2 = strtod (subtoken, &endptr);
    if (amp_beat2 == 0.0)
    {
      if (errno != 0)             //  error
        error ("Amplitude beat2 for binaural had an error.\n");
    }
    binaural1->amp_beat2 = amp_beat2;

    subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
    errno = 0;
    double amp_pct1 = strtod (subtoken, &endptr);
    if (amp_pct1 == 0.0)
    {
      if (errno != 0)             //  error
        error ("Amplitude adj1 for binaural had an error.\n");
    }
    binaural1->amp_pct1 = AMP_AD(amp_pct1);

    subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
    errno = 0;
    double amp_pct2 = strtod (subtoken, &endptr);
    if (amp_pct2 == 0.0)
    {
      if (errno != 0)             //  error
        error ("Amplitude adj2 for binaural had an error.\n");
    }
    binaural1->amp_pct2 = AMP_AD(amp_pct2);
  }

  subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
  if (subtoken != NULL && strcmp (subtoken, ">") == 0)
    binaural1->slide = 1;
}

/* Set up a bell sequence */

void
setup_bell (char *token, void **work)
{
  char *endptr;
  char *subtoken;
  char *str2 = NULL;
  char *saveptr2;
  bell *bell1 = NULL;

  bell1 = (bell *) Alloc (sizeof (bell) * 1);
  *work = bell1;
  bell1->next = NULL;
  bell1->type = 2;
  bell1->off1 = 0;  // begin at 0 degrees
  str2 = token;
  subtoken = strtok_r (str2, separators, &saveptr2);        // remove voice type
  str2 = NULL;

  subtoken = strtok_r (str2, separators, &saveptr2);        // get subtoken of token
  errno = 0;
  double carrier = strtod (subtoken, &endptr);
  if (carrier == 0.0)
  {
    if (errno == 0)             // no errors
      error ("Carrier for bell cannot be 0.\n");
    else                        // there was an error
      error ("Carrier for bell had an error.\n");
  }
  bell1->carrier = carrier;

  subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
  errno = 0;
  double amp_min = strtod (subtoken, &endptr);
  if (amp_min == 0.0)
  {
    if (errno != 0)             //  error
      error ("Amplitude_min for bell had an error.\n");
  }
  bell1->amp_min = AMP_AD(amp_min);

  subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
  errno = 0;
  double amp_max = strtod (subtoken, &endptr);
  if (amp_max == 0.0)
  {
    if (errno != 0)             //  error
      error ("Amplitude_max for bell had an error.\n");
  }
  bell1->amp_max = AMP_AD(amp_max);

  subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
  errno = 0;
  double split_begin = strtod (subtoken, &endptr);
  if ((split_begin < 0.0 && split_begin != -1.0) || split_begin > 1.0)
  {
    if (errno != 0)             //  error
      error ("Split_begin for bell had an error.\n");
    else
      split_begin = 0.5;
  }
  bell1->split_begin = split_begin;

  subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
  errno = 0;
  double split_end = strtod (subtoken, &endptr);
  if ((split_end < 0.0 && split_end != -1.0) || split_end > 1.0)
  {
    if (errno != 0)             //  error
      error ("Split_end for bell had an error.\n");
    else
      split_end = 0.5;
  }
  bell1->split_end = split_end;

  subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
  errno = 0;
  double split_low = strtod (subtoken, &endptr);
  if (split_low < 0.0 || split_low > 1.0)
  {
    if (errno != 0)             //  error
      error ("Split_low for bell had an error.\n");
    else
      split_low = 0.5;
  }
  bell1->split_low = split_low;

  subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
  errno = 0;
  double split_high = strtod (subtoken, &endptr);
  if (split_high < 0.0 || split_high > 1.0)
  {
    if (errno != 0)             //  error
      error ("Split_high for bell had an error.\n");
    else
      split_high = 0.5;
  }
  bell1->split_high = split_high;

  subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
  errno = 0;
  double length_min = strtod (subtoken, &endptr);

  if (length_min == 0.0)
  {
    if (errno != 0)             //  error
      error ("Length_min for bell had an error.\n");
  }
  bell1->length_min = length_min * out_rate;      // convert to frames from seconds
  subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
  errno = 0;
  double length_max = strtod (subtoken, &endptr);
  if (length_max == 0.0)
  {
    if (errno != 0)             //  error
      error ("Length_max for bell had an error.\n");
  }
  bell1->length_max = length_max * out_rate;      // convert to frames from seconds

  subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
  errno = 0;
  double repeat_min = strtod (subtoken, &endptr);
  if (repeat_min == 0.0)
  {
    if (errno != 0)             //  error
      error ("Repeat_min for bell had an error.\n");
  }
  bell1->repeat_min = repeat_min * out_rate;      // convert to frames from seconds

  subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
  errno = 0;
  double repeat_max = strtod (subtoken, &endptr);
  if (repeat_max == 0.0)
  {
    if (errno != 0)             //  error
      error ("Repeat_max for bell had an error.\n");
  }
  bell1->repeat_max = repeat_max * out_rate;      // convert to frames from seconds

  subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
  errno = 0;
  double behave = strtod (subtoken, &endptr);
  if (behave <= 0.0 || behave >= 6.0)
  {
    if (errno != 0)             //  error
      error ("Behave for bell had an error.\n");
    else
      behave = 3;
  }
  bell1->behave = (int) behave;   // convert to int

  /* create the time to first play of bell */
  if (bell1->repeat_min == bell1->repeat_max)
    bell1->next_play = bell1->repeat_min;      // fixed period
  else
  {
    int_64 delta = (int_64) ( (drand48 ()) * (bell1->repeat_max - bell1->repeat_min));
    bell1->next_play = bell1->repeat_min + delta;      // frames to next play
  }
  bell1->sofar = 0LL;
}

/* Set up a noise sequence */

int
setup_noise (char *token, void **work)
{
  char *endptr;
  char *subtoken;
  char *str2 = NULL;
  char *saveptr2;
  noise *noise1 = NULL;

  noise1 = (noise *) Alloc (sizeof (noise) * 1);
  *work = noise1;
  noise1->next = NULL;
  noise1->type = 3;
  noise1->off1 = 0;  // begin at 0 degrees
  str2 = token;
  subtoken = strtok_r (str2, separators, &saveptr2);        // remove voice type
  str2 = NULL;

  subtoken = strtok_r (str2, separators, &saveptr2);        // get subtoken of token
  errno = 0;
  double carrier_min = strtod (subtoken, &endptr);
  if (carrier_min == 0.0)
  {
    if (errno == 0)             // no errors
      error ("Carrier_min for noise cannot be 0.\n");
    else                        // there was an error
      error ("Carrier_min for noise had an error.\n");
  }
  noise1->carrier_min = carrier_min;
  
  subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
  errno = 0;
  double carrier_max = strtod (subtoken, &endptr);
  if (carrier_max == 0.0)
  {
    if (errno == 0)             // no errors
      error ("Carrier_max for noise cannot be 0.\n");
    else                        // there was an error
      error ("Carrier_max for noise had an error.\n");
  }
  noise1->carrier_max = carrier_max;

  subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
  errno = 0;
  double amp_min = strtod (subtoken, &endptr);
  if (amp_min == 0.0)
  {
    if (errno != 0)             //  error
      error ("Amplitude_min for noise had an error.\n");
  }
  noise1->amp_min = AMP_AD(amp_min);

  subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
  errno = 0;
  double amp_max = strtod (subtoken, &endptr);
  if (amp_max == 0.0)
  {
    if (errno != 0)             //  error
      error ("Amplitude_max for noise had an error.\n");
  }
  noise1->amp_max = AMP_AD(amp_max);

  subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
  errno = 0;
  double split_begin = strtod (subtoken, &endptr);
  if ((split_begin < 0.0 && split_begin != -1.0) || split_begin > 1.0)
  {
    if (errno != 0)             //  error
      error ("Split_begin for noise had an error.\n");
    else
      split_begin = 0.5;
  }
  noise1->split_begin = split_begin;

  subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
  errno = 0;
  double split_end = strtod (subtoken, &endptr);
  if ((split_end < 0.0 && split_end != -1.0) || split_end > 1.0)
  {
    if (errno != 0)             //  error
      error ("Split_end for noise had an error.\n");
    else
      split_end = 0.5;
  }
  noise1->split_end = split_end;

  subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
  errno = 0;
  double split_low = strtod (subtoken, &endptr);
  if (split_low == 0.0)
  {
    if (errno != 0)             //  error
      error ("Split_low for noise had an error.\n");
    else
      split_low = 0.5;
  }
  noise1->split_low = split_low;

  subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
  errno = 0;
  double split_high = strtod (subtoken, &endptr);
  if (split_high == 0.0)
  {
    if (errno != 0)             //  error
      error ("Split_high for noise had an error.\n");
    else
      split_high = 0.5;
  }
  noise1->split_high = split_high;

  subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
  errno = 0;
  double length_min = strtod (subtoken, &endptr);
  if (length_min == 0.0)
  {
    if (errno != 0)             //  error
      error ("Length_min for noise had an error.\n");
  }
  noise1->length_min = (int_64) (length_min * out_rate);      // convert to frames from seconds

  subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
  errno = 0;
  double length_max = strtod (subtoken, &endptr);
  if (length_max == 0.0)
  {
    if (errno != 0)             //  error
      error ("Length_max for noise had an error.\n");
  }
  noise1->length_max = (int_64) (length_max * out_rate);      // convert to frames from seconds

  subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
  errno = 0;
  double repeat_min = strtod (subtoken, &endptr);
  if (repeat_min == 0.0)
  {
    if (errno != 0)             //  error
      error ("Repeat_min for noise had an error.\n");
  }
  noise1->repeat_min = (int_64) (repeat_min * out_rate);      // convert to frames from seconds

  subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
  errno = 0;
  double repeat_max = strtod (subtoken, &endptr);
  if (repeat_max == 0.0)
  {
    if (errno != 0)             //  error
      error ("Repeat_max for noise had an error.\n");
  }
  noise1->repeat_max = (int_64) (repeat_max * out_rate);      // convert to frames from seconds

  subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
  errno = 0;
  double behave_low = strtod (subtoken, &endptr);
  if (behave_low == 0.0)
  {
    if (errno != 0)             //  error
      error ("Behave_low for noise had an error.\n");
  }
  noise1->behave_low = (int) behave_low;   // convert to int

  subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
  errno = 0;
  double behave_high = strtod (subtoken, &endptr);
  if (behave_high == 0.0)
  {
    if (errno != 0)             //  error
      error ("Behave_high for noise had an error.\n");
  }
  noise1->behave_high = (int) behave_high;         // convert to int
    /* possible multiplier for a noise voice */
  subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
  double multiple = 0.0;
  if (subtoken)  // not null
  {
    errno = 0;
    multiple = strtod (subtoken, &endptr);
    if (multiple == 0.0)
    {
      if (errno != 0)             //  error
        error ("Multiple for noise had an error.\n");
      else
        multiple = 1.0;
    }
  }
  else
    multiple = 1.0;
  /* create the time to first play of noise */
  noise1->sofar = 0LL;
  if (noise1->repeat_min == noise1->repeat_max)
    noise1->next_play = noise1->repeat_min;      // fixed period
  else
  {
    int_64 delta = (int_64) ( (drand48 ()) * (noise1->repeat_max - noise1->repeat_min));
    noise1->next_play = noise1->repeat_min + delta;      // frames to next play
  }
  return abs ((int) multiple);         // convert to int
}

/* Set up a stoch file sequence */

void
setup_stoch (char *token, void **work)
{
  char *endptr;
  char *subtoken;
  char *str2 = NULL;
  char *saveptr2;
  char filename [256];
  stoch *stoch1 = NULL;
  SNDFILE *sndfile;
  SF_INFO sfinfo;
  sf_count_t num_frames;
  int subformat ;
  short holder, peak=0;
  int k;

  stoch1 = (stoch *) Alloc (sizeof (stoch) * 1);
  *work = stoch1;
  stoch1->next = NULL;
  stoch1->type = 4;
  stoch1->off1 = 0;
  str2 = token;
  subtoken = strtok_r (str2, separators, &saveptr2);        // remove voice type
  str2 = NULL;
  subtoken = strtok_r (str2, separators, &saveptr2);        // get subtoken of token
  /* subtoken is file name for stoch sound */
  strcpy (filename, subtoken);
  check_samplerate (filename);  // if filename is not same rate as out_rate, resample to new file
  if (! (sndfile = sf_open (filename, SFM_READ, &sfinfo)))
    error ("Couldn't open stoch file %s\n", filename);
  if (sfinfo.channels == 1)
  {
    stoch1->channels = sfinfo.channels;  // mono
    stoch1->mono = 1;  // mono
  }
  else if (sfinfo.channels == 2)  // check if mono in stereo format
  {
    stoch1->channels = 2;  // stereo channels
    double peaks[2];
    int retval = sf_command (sndfile, SFC_CALC_MAX_ALL_CHANNELS, peaks, sizeof (peaks));
    if (retval == 0)
      if (peaks [0] < 1e-10)  // a mute channel
        stoch1->mono = 2;  // right channel has sound
      else if (peaks [1] < 1e-10)  // a mute channel
        stoch1->mono = 1;  // left channel has sound
      else if (peaks[0] / peaks [1] > 100)  // large imbalance
        stoch1->mono = 1;  // left channel has sound
      else if (peaks[1] / peaks [0] > 100)  // large imbalance
        stoch1->mono = 2;  // right channel has sound
      else
        stoch1->mono = 0;
    else
      stoch1->mono = 0;
  }
  else
    error ("Stoch file %s has incorrect number of channels %d\n", 
            subtoken, sfinfo.channels);
  num_frames = sf_seek (sndfile, 0, SEEK_END);
  stoch1->frames = num_frames;
  stoch1->sound = (short *) Alloc ((sizeof (short)) * num_frames * sfinfo.channels);
  sf_seek (sndfile, 0, SEEK_SET);
  subformat = sfinfo.format & SF_FORMAT_SUBMASK ;
  if (subformat == SF_FORMAT_FLOAT || subformat == SF_FORMAT_DOUBLE)
  {	double	scale ;

    sf_command (sndfile, SFC_CALC_SIGNAL_MAX, &scale, sizeof (scale)) ;
    if (scale < 1e-10)
      scale = 1.0 ;
    else
      scale = 32700.0 / scale ;
    sf_command (sndfile, SFC_SET_SCALE_FLOAT_INT_READ, NULL, SF_TRUE) ;
    /* reading into short */
    num_frames = sf_readf_short (sndfile, stoch1->sound, stoch1->frames);
  }
  else // reading into short
    num_frames = sf_readf_short (sndfile, stoch1->sound, stoch1->frames);
  if (num_frames != stoch1->frames)
    error ("Read incorrect number of frames for stoch file %s, %ld instead of %ld\n", 
            subtoken, num_frames, stoch1->frames);
  sf_close (sndfile);

  /* find the maximum amplitude in the sound file, always short int once read */
  for (k = 0 ; k < stoch1->frames ; k += stoch1->channels)
  { 
    holder = abs (stoch1->sound [k]) ;
    peak  = holder > peak ? holder : peak ;
    if (stoch1->channels == 2)
    {
      holder = abs (stoch1->sound [k+1]) ;
      peak  = holder > peak ? holder : peak ;
    }
  } 
  // scale factor is 1 divided by maximum amplitude in file
  stoch1->scale = 1.0 / ((double) peak + 10.0);  
                                    
  subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
  errno = 0;
  double amp_min = strtod (subtoken, &endptr);
  if (amp_min == 0.0)
  {
    if (errno != 0)             //  error
      error ("Amplitude_min for stoch had an error.\n");
  }
  stoch1->amp_min = AMP_AD(amp_min);

  subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
  errno = 0;
  double amp_max = strtod (subtoken, &endptr);
  if (amp_max == 0.0)
  {
    if (errno != 0)             //  error
      error ("Amplitude_max for stoch had an error.\n");
  }
  stoch1->amp_max = AMP_AD(amp_max);

  subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
  errno = 0;
  double split_begin = strtod (subtoken, &endptr);
  if ((split_begin < 0.0 && split_begin != -1.0) || split_begin > 1.0)
  {
    if (errno != 0)             //  error
      error ("Split_begin for stoch had an error.\n");
    else
      split_begin = 0.5;
  }
  stoch1->split_begin = split_begin;

  subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
  errno = 0;
  double split_end = strtod (subtoken, &endptr);
  if ((split_end < 0.0 && split_end != -1.0) || split_end > 1.0)
  {
    if (errno != 0)             //  error
      error ("Split_end for stoch had an error.\n");
    else
      split_end = 0.5;
  }
  stoch1->split_end = split_end;

  subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
  errno = 0;
  double split_low = strtod (subtoken, &endptr);
  if (split_low == 0.0)
  {
    if (errno != 0)             //  error
      error ("Split_low for stoch had an error.\n");
  }
  stoch1->split_low = split_low;

  subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
  errno = 0;
  double split_high = strtod (subtoken, &endptr);
  if (split_high == 0.0)
  {
    if (errno != 0)             //  error
      error ("Split_high for stoch had an error.\n");
  }
  stoch1->split_high = split_high;

  subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
  errno = 0;
  double repeat_min = strtod (subtoken, &endptr);
  if (repeat_min == 0.0)
  {
    if (errno != 0)             //  error
      error ("Repeat_min for stoch had an error.\n");
  }
  stoch1->repeat_min = (int_64) (repeat_min * out_rate);      // convert to frames from seconds

  subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
  errno = 0;
  double repeat_max = strtod (subtoken, &endptr);
  if (repeat_max == 0.0)
  {
    if (errno != 0)             //  error
      error ("Repeat_max for stoch had an error.\n");
  }
  stoch1->repeat_max = (int_64) (repeat_max * out_rate);      // convert to frames from seconds
  /* set up first play of stoch */
  stoch1->sofar = 0LL;
  if (stoch1->repeat_min == stoch1->repeat_max)
  {
    int_64 delta = (int_64) ( (drand48 ()) * (stoch1->repeat_min));
    stoch1->next_play = delta;      // fixed period, start with random play
  }
  else
  {
    int_64 delta = (int_64) ( (drand48 ()) * (stoch1->repeat_max - stoch1->repeat_min));
    stoch1->next_play = delta;      // frames to next play
  }
}

/* Set up a sample file sequence */

void
setup_sample (char *token, void **work)
{
  char *endptr;
  char *subtoken;
  char *str2 = NULL;
  char *saveptr2;
  char filename [256];
  sample *sample1 = NULL;
  SNDFILE *sndfile;
  SF_INFO sfinfo;
  sf_count_t num_frames;
  int subformat ;
  short holder, peak=0;
  int k;

  sample1 = (sample *) Alloc (sizeof (sample) * 1);
  *work = sample1;
  sample1->next = NULL;
  sample1->type = 5;
  str2 = token;
  subtoken = strtok_r (str2, separators, &saveptr2);        // remove voice type
  str2 = NULL;
  subtoken = strtok_r (str2, separators, &saveptr2);        // get subtoken of token
  /* subtoken is file name for sample sound */
  strcpy (filename, subtoken);
  check_samplerate (filename);  // if filename is not same rate as out_rate, resample to new file
  if (! (sndfile = sf_open (filename, SFM_READ, &sfinfo)))
    error ("Couldn't open sample file %s\n", filename);
  if (sfinfo.channels == 1)
  {
    sample1->channels = sfinfo.channels;  // mono
    sample1->mono = 1;  // mono
  }
  else if (sfinfo.channels == 2)  // check if mono in stereo format
  {
    sample1->channels = 2;  // stereo channels
    double peaks[2];
    int retval = sf_command (sndfile, SFC_CALC_MAX_ALL_CHANNELS, peaks, sizeof (peaks));
    if (retval == 0)
      if (peaks [0] < 1e-10)  // a mute channel
        sample1->mono = 2;  // right channel has sound
      else if (peaks [1] < 1e-10)  // a mute channel
        sample1->mono = 1;  // left channel has sound
      else if (peaks[0] / peaks [1] > 100)  // large imbalance
        sample1->mono = 1;  // left channel has sound
      else if (peaks[1] / peaks [0] > 100)  // large imbalance
        sample1->mono = 2;  // right channel has sound
      else
        sample1->mono = 0;
    else
      sample1->mono = 0;
  }
  else
    error ("Sample file %s has incorrect number of channels %d\n", 
            subtoken, sfinfo.channels);
  num_frames = sf_seek (sndfile, 0, SEEK_END);
  sample1->frames = num_frames;
  sample1->sound = (short *) Alloc ((sizeof (short)) * num_frames * sfinfo.channels);
  sf_seek (sndfile, 0, SEEK_SET);
  subformat = sfinfo.format & SF_FORMAT_SUBMASK ;
  if (subformat == SF_FORMAT_FLOAT || subformat == SF_FORMAT_DOUBLE)
  {	double	scale ;

    sf_command (sndfile, SFC_CALC_SIGNAL_MAX, &scale, sizeof (scale)) ;
    if (scale < 1e-10)
      scale = 1.0 ;
    else
      scale = 32700.0 / scale ;
    sf_command (sndfile, SFC_SET_SCALE_FLOAT_INT_READ, NULL, SF_TRUE) ;
    /* reading into short */
    num_frames = sf_readf_short (sndfile, sample1->sound, sample1->frames);
  }
  else /* reading into short */
    num_frames = sf_readf_short (sndfile, sample1->sound, sample1->frames);
  if (num_frames != sample1->frames)
    error ("Read incorrect number of frames for sample file %s, %ld instead of %ld\n", 
            subtoken, num_frames, sample1->frames);
  sf_close (sndfile);

  /* find the maximum amplitude in the sound file */
  for (k = 0 ; k < sample1->frames ; k += sample1->channels)
  { 
    holder = abs (sample1->sound [k]) ;
    peak  = holder > peak ? holder : peak ;
    if (sample1->channels == 2)
    {
      holder = abs (sample1->sound [k+1]) ;
      peak  = holder > peak ? holder : peak ;
    }
  } 
  // scale factor is 1 divided by maximum amplitude in file
  sample1->scale = 1.0 / ((double) peak + 10.0);  
                                    
  subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
  errno = 0;
  double amp_min = strtod (subtoken, &endptr);
  if (amp_min == 0.0)
  {
    if (errno != 0)             //  error
      error ("Amplitude_min for sample had an error.\n");
  }
  sample1->amp_min = AMP_AD(amp_min);

  subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
  errno = 0;
  double amp_max = strtod (subtoken, &endptr);
  if (amp_max == 0.0)
  {
    if (errno != 0)             //  error
      error ("Amplitude_max for sample had an error.\n");
  }
  sample1->amp_max = AMP_AD(amp_max);

  subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
  errno = 0;
  double split_begin = strtod (subtoken, &endptr);
  if ((split_begin < 0.0 && split_begin != -1.0) || split_begin > 1.0)
  {
    if (errno != 0)             //  error
      error ("Split_begin for sample had an error.\n");
    else
      split_begin = 0.5;
  }
  sample1->split_begin = split_begin;

  subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
  errno = 0;
  double split_end = strtod (subtoken, &endptr);
  if ((split_end < 0.0 && split_end != -1.0) || split_end > 1.0)
  {
    if (errno != 0)             //  error
      error ("Split_end for sample had an error.\n");
    else
      split_end = 0.5;
  }
  sample1->split_end = split_end;

  subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
  errno = 0;
  double split_low = strtod (subtoken, &endptr);
  if (split_low == 0.0)
  {
    if (errno != 0)             //  error
      error ("Split_low for sample had an error.\n");
  }
  sample1->split_low = split_low;

  subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
  errno = 0;
  double split_high = strtod (subtoken, &endptr);
  if (split_high == 0.0)
  {
    if (errno != 0)             //  error
      error ("Split_high for sample had an error.\n");
  }
  sample1->split_high = split_high;
  subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
  errno = 0;
  double size = strtod (subtoken, &endptr);

  if (size == 0.0)
  {
    if (errno != 0)             //  error
      error ("Play size for sample had an error.\n");
  }
  sample1->size = (int_64) (size * out_rate);  // convert from seconds to frames 
  /* Create the first sample position */
  sample1->sofar = 0LL;  // how much has played so far
  /* allow random position from 0 to length - frames in sample */
  sample1->off1 = (int_64) (drand48 ()) * (sample1->frames - sample1->size);
  sample1->play = sample1->size;  // start out playing at above offset
  sample1->amp = (sample1->amp_min + sample1->amp_max)/2;  // start amp is average
  sample1->split_now = (sample1->split_low + sample1->split_high)/2;  // start split is average
}

/* Set up a repeat file sequence */

void
setup_repeat (char *token, void **work)
{
  char *endptr;
  char *subtoken;
  char *str2 = NULL;
  char *saveptr2;
  char filename [256];
  repeat *repeat1 = NULL;
  SNDFILE *sndfile;
  SF_INFO sfinfo;
  sf_count_t num_frames;
  int subformat ;
  short holder, peak=0;
  int k;

  repeat1 = (repeat *) Alloc (sizeof (repeat) * 1);
  *work = repeat1;
  repeat1->next = NULL;
  repeat1->type = 6;
  str2 = token;
  subtoken = strtok_r (str2, separators, &saveptr2);        // remove voice type
  str2 = NULL;
  subtoken = strtok_r (str2, separators, &saveptr2);        // get subtoken of token
  /* subtoken is file name for repeat sound */
  strcpy (filename, subtoken);
  check_samplerate (filename);  // if filename is not same rate as out_rate, resample to new file
  if (! (sndfile = sf_open (filename, SFM_READ, &sfinfo)))
    error ("Couldn't open repeat file %s\n", filename);
  if (sfinfo.channels == 1)
  {
    repeat1->channels = sfinfo.channels;  // mono
    repeat1->mono = 1;  // mono
  }
  else if (sfinfo.channels == 2)  // check if mono in stereo format
  {
    repeat1->channels = 2;  // stereo channels
    double peaks[2];
    int retval = sf_command (sndfile, SFC_CALC_MAX_ALL_CHANNELS, peaks, sizeof (peaks));
    if (retval == 0)
      if (peaks [0] < 1e-10)  // a mute channel
        repeat1->mono = 2;  // right channel has sound
      else if (peaks [1] < 1e-10)  // a mute channel
        repeat1->mono = 1;  // left channel has sound
      else if (peaks[0] / peaks [1] > 100)  // large imbalance
        repeat1->mono = 1;  // left channel has sound
      else if (peaks[1] / peaks [0] > 100)  // large imbalance
        repeat1->mono = 2;  // right channel has sound
      else
        repeat1->mono = 0;
    else
      repeat1->mono = 0;
  }
  else
    error ("Repeat file %s has incorrect number of channels %d\n", 
            subtoken, sfinfo.channels);
  num_frames = sf_seek (sndfile, 0, SEEK_END);
  repeat1->frames = num_frames;
  repeat1->sound = (short *) Alloc ((sizeof (short)) * num_frames * sfinfo.channels);
  sf_seek (sndfile, 0, SEEK_SET);
  subformat = sfinfo.format & SF_FORMAT_SUBMASK ;
  if (subformat == SF_FORMAT_FLOAT || subformat == SF_FORMAT_DOUBLE)
  {	double	scale ;

    sf_command (sndfile, SFC_CALC_SIGNAL_MAX, &scale, sizeof (scale)) ;
    if (scale < 1e-10)
      scale = 1.0 ;
    else
      scale = 32700.0 / scale ;
    sf_command (sndfile, SFC_SET_SCALE_FLOAT_INT_READ, NULL, SF_TRUE) ;
    /* reading into short */
    num_frames = sf_readf_short (sndfile, repeat1->sound, repeat1->frames);
  }
  else /* reading into short */
    num_frames = sf_readf_short (sndfile, repeat1->sound, repeat1->frames);
  if (num_frames != repeat1->frames)
    error ("Read incorrect number of frames for repeat file %s, %ld instead of %ld\n", 
            subtoken, num_frames, repeat1->frames);
  sf_close (sndfile);

  /* find the maximum amplitude in the sound file */
  for (k = 0 ; k < repeat1->frames ; k += repeat1->channels)
  { 
    holder = abs (repeat1->sound [k]) ;
    peak  = holder > peak ? holder : peak ;
    if (repeat1->channels == 2)
    {
      holder = abs (repeat1->sound [k+1]) ;
      peak  = holder > peak ? holder : peak ;
    }
  } 
  // scale factor is 1 divided by maximum amplitude in file
  repeat1->scale = 1.0 / ((double) peak + 10.0);
                                    
  subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
  errno = 0;
  double amp_min = strtod (subtoken, &endptr);
  if (amp_min == 0.0)
  {
    if (errno != 0)             //  error
      error ("Amplitude_min for repeat had an error.\n");
  }
  repeat1->amp_min = AMP_AD(amp_min);

  subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
  errno = 0;
  double amp_max = strtod (subtoken, &endptr);
  if (amp_max == 0.0)
  {
    if (errno != 0)             //  error
      error ("Amplitude_max for repeat had an error.\n");
  }
  repeat1->amp_max = AMP_AD(amp_max);

  subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
  errno = 0;
  double split_begin = strtod (subtoken, &endptr);
  if ((split_begin < 0.0 && split_begin != -1.0) || split_begin > 1.0)
  {
    if (errno != 0)             //  error
      error ("Split_begin for repeat had an error.\n");
    else
      split_begin = 0.5;
  }
  repeat1->split_begin = split_begin;

  subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
  errno = 0;
  double split_end = strtod (subtoken, &endptr);
  if ((split_end < 0.0 && split_end != -1.0) || split_end > 1.0)
  {
    if (errno != 0)             //  error
      error ("Split_end for repeat had an error.\n");
    else
      split_end = 0.5;
  }
  repeat1->split_end = split_end;

  subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
  errno = 0;
  double split_low = strtod (subtoken, &endptr);
  if (split_low == 0.0)
  {
    if (errno != 0)             //  error
      error ("Split_low for repeat had an error.\n");
  }
  repeat1->split_low = split_low;
  subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
  errno = 0;
  double split_high = strtod (subtoken, &endptr);
  if (split_high == 0.0)
  {
    if (errno != 0)             //  error
      error ("Split_high for repeat had an error.\n");
  }
  repeat1->split_high = split_high;
  /* set our position in the repeat file */
  repeat1->sofar = 0LL;  // how much has played so far
  repeat1->off1 = 0;  // start from start of file
  repeat1->play = repeat1->frames;  // start out playing at above offset
  repeat1->amp = (repeat1->amp_min + repeat1->amp_max)/2;  // start amp is average
  repeat1->split_now = (repeat1->split_low + repeat1->split_high)/2;  // start split is average
}

/* Set up a once file sequence */

void
setup_once (char *token, void **work)
{
  char *endptr;
  char *subtoken;
  char *str2 = NULL;
  char *saveptr2;
  char filename [256];
  once *once1 = NULL;
  SNDFILE *sndfile;
  SF_INFO sfinfo;
  sf_count_t num_frames;
  int subformat ;
  short holder, peak=0;
  int k;

  once1 = (once *) Alloc (sizeof (once) * 1);
  *work = once1;
  once1->next = NULL;
  once1->type = 7;
  once1->off1 = 0;
  str2 = token;
  subtoken = strtok_r (str2, separators, &saveptr2);        // remove voice type
  str2 = NULL;
  subtoken = strtok_r (str2, separators, &saveptr2);        // get subtoken of token
  /* subtoken is file name for once sound */
  strcpy (filename, subtoken);
  check_samplerate (filename);  // if filename is not same rate as out_rate, resample to new file
  if (! (sndfile = sf_open (filename, SFM_READ, &sfinfo)))
    error ("Couldn't open once file %s\n", filename);
  if (sfinfo.channels == 1)
  {
    once1->channels = sfinfo.channels;  // mono
    once1->mono = 1;  // mono
  }
  else if (sfinfo.channels == 2)  // check if mono in stereo format
  {
    once1->channels = 2;  // stereo channels
    double peaks[2];
    int retval = sf_command (sndfile, SFC_CALC_NORM_MAX_ALL_CHANNELS, peaks, sizeof (peaks));
    if (retval == 0)
      if (peaks [0] < 1e-10)  // a mute channel
        once1->mono = 2;  // right channel has sound
      else if (peaks [1] < 1e-10)  // a mute channel
        once1->mono = 1;  // left channel has sound
      else if (peaks[0] / peaks [1] > 100)  // large imbalance
        once1->mono = 1;  // left channel has sound
      else if (peaks[1] / peaks [0] > 100)  // large imbalance
        once1->mono = 2;  // right channel has sound
      else
        once1->mono = 0;
    else
      once1->mono = 0;
  }
  else
    error ("Once file %s has incorrect number of channels %d\n", 
            subtoken, sfinfo.channels);
  num_frames = sf_seek (sndfile, 0, SEEK_END);
  once1->frames = num_frames;
  once1->sound = (short *) Alloc ((sizeof (short)) * num_frames * sfinfo.channels);
  sf_seek (sndfile, 0, SEEK_SET);
  subformat = sfinfo.format & SF_FORMAT_SUBMASK ;
  if (subformat == SF_FORMAT_FLOAT || subformat == SF_FORMAT_DOUBLE)
  {	double	scale ;

    sf_command (sndfile, SFC_CALC_SIGNAL_MAX, &scale, sizeof (scale)) ;
    if (scale < 1e-10)
      scale = 1.0 ;
    else
      scale = 32700.0 / scale ;
    sf_command (sndfile, SFC_SET_SCALE_FLOAT_INT_READ, NULL, SF_TRUE) ;
    /* reading into short */
    num_frames = sf_readf_short (sndfile, once1->sound, once1->frames);
  }
  else // reading into short
    num_frames = sf_readf_short (sndfile, once1->sound, once1->frames);
  if (num_frames != once1->frames)
    error ("Read incorrect number of frames for once file %s, %ld instead of %ld\n", 
            subtoken, num_frames, once1->frames);
  sf_close (sndfile);

  /* find the maximum amplitude in the sound file */
  for (k = 0 ; k < once1->frames ; k += once1->channels)
  { 
    holder = abs (once1->sound [k]) ;
    peak  = holder > peak ? holder : peak ;
    if (once1->channels == 2)
    {
      holder = abs (once1->sound [k+1]) ;
      peak  = holder > peak ? holder : peak ;
    }
  } 
  // scale factor is 1 divided by maximum amplitude in file
  once1->scale = 1.0 / ((double) peak + 10.0);  
                                    
  subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
  errno = 0;
  double amp_min = strtod (subtoken, &endptr);
  if (amp_min == 0.0)
  {
    if (errno != 0)             //  error
      error ("Amplitude_min for once had an error.\n");
  }
  once1->amp_min = AMP_AD(amp_min);

  subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
  errno = 0;
  double amp_max = strtod (subtoken, &endptr);
  if (amp_max == 0.0)
  {
    if (errno != 0)             //  error
      error ("Amplitude_max for once had an error.\n");
  }
  once1->amp_max = AMP_AD(amp_max);

  subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
  errno = 0;
  double split_begin = strtod (subtoken, &endptr);
  if ((split_begin < 0.0 && split_begin != -1.0) || split_begin > 1.0)
  {
    if (errno != 0)             //  error
      error ("Split_begin for once had an error.\n");
    else
      split_begin = 0.5;
  }
  once1->split_begin = split_begin;

  subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
  errno = 0;
  double split_end = strtod (subtoken, &endptr);
  if ((split_end < 0.0 && split_end != -1.0) || split_end > 1.0)
  {
    if (errno != 0)             //  error
      error ("Split_end for once had an error.\n");
    else
      split_end = 0.5;
  }
  once1->split_end = split_end;

  subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
  errno = 0;
  double split_low = strtod (subtoken, &endptr);
  if (split_low == 0.0)
  {
    if (errno != 0)             //  error
      error ("Split_low for once had an error.\n");
  }
  once1->split_low = split_low;

  subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
  errno = 0;
  double split_high = strtod (subtoken, &endptr);
  if (split_high == 0.0)
  {
    if (errno != 0)             //  error
      error ("Split_high for once had an error.\n");
  }
  once1->split_high = split_high;

  subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
  errno = 0;
  double play_when = strtod (subtoken, &endptr);
  if (play_when == 0.0)
  {
    if (errno != 0)             //  error
      error ("Play_when for once had an error.\n");
  }
  once1->play_when = (int_64) (play_when * out_rate);      // convert to frames from seconds

  /* set up play of once */
  once1->sofar = 0LL;
  once1->next_play = once1->play_when;  // single play of file at play_when
}

/* Set up a chronaural sequence */

void
setup_chronaural (char *token, void **work)
{
  char *endptr;
  char *subtoken;
  char *str2 = NULL;
  char *saveptr2;
  chronaural *chronaural1 = NULL;

  chronaural1 = (chronaural *) Alloc ((sizeof (chronaural)) * 1);
  *work = (void *) chronaural1;
  chronaural1->next = NULL;
  chronaural1->type = 8;
  chronaural1->slide = 0;  // default to not slide
  chronaural1->off1 = chronaural1->off2 = 0;  // begin at 0 degrees
  chronaural1->last_off1 = chronaural1->last_off2 = NULL;  // no previous voice offsets yet
  chronaural1->first_pass = 1;  // inactive
  str2 = token;

  subtoken = strtok_r (str2, separators, &saveptr2);        // remove voice type
  str2 = NULL;
  
  subtoken = strtok_r (str2, separators, &saveptr2);        // get subtoken of token
  errno = 0;
  double carrier = strtod (subtoken, &endptr);
  if (carrier == 0.0)
  {
    if (errno == 0)             // no errors
      error ("Carrier for chronaural cannot be 0.\n");
    else                        // there was an error
      error ("Carrier for chronaural had an error.\n");
  }
  chronaural1->carrier = carrier;

  subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
  errno = 0;
  double amp = strtod (subtoken, &endptr);
  if (amp == 0.0)
  {
    if (errno != 0)             //  error
      error ("Amplitude for chronaural had an error.\n");
  }
  chronaural1->amp = AMP_AD(amp);

  subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
  errno = 0;
  double amp_beat = strtod (subtoken, &endptr);
  if (amp_beat == 0.0)
  {
    if (errno != 0)             //  error
      error ("Amplitude beat for chronaural had an error.\n");
  }
  chronaural1->amp_beat = amp_beat;

  subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
  errno = 0;
  double amp_fraction = strtod (subtoken, &endptr);
  if (amp_fraction == 0.0)
  {
    if (errno != 0)             //  error
      error ("Amplitude fraction for chronaural had an error.\n");
  }
  chronaural1->amp_fraction = amp_fraction;

  subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
  errno = 0;
  double amp_behave = strtod (subtoken, &endptr);
  if (amp_behave == 0.0)
  {
    if (errno != 0)             //  error
      error ("Amplitude behave for chronaural had an error.\n");
  }
  chronaural1->amp_behave = amp_behave;

  subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
  errno = 0;
  double split_begin = strtod (subtoken, &endptr);
  if ((split_begin < 0.0 && split_begin != -1.0) || split_begin > 1.0)
  {
    if (errno != 0)             //  error
      error ("Split_begin for chronaural had an error.\n");
    else
      split_begin = 0.5;
  }
  chronaural1->split_begin = split_begin;

  subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
  errno = 0;
  double split_end = strtod (subtoken, &endptr);
  if ((split_end < 0.0 && split_end != -1.0) || split_end > 1.0)
  {
    if (errno != 0)             //  error
      error ("Split_end for chronaural had an error.\n");
    else
      split_end = 0.5;
  }
  chronaural1->split_end = split_end;

  subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
  errno = 0;
  double split_low = strtod (subtoken, &endptr);
  if (split_low < 0.0 || split_low > 1.0)
  {
    if (errno != 0)             //  error
      error ("Split_low for chronaural had an error.\n");
    else
      split_low = 0.5;
  }
  chronaural1->split_low = split_low;

  subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
  errno = 0;
  double split_high = strtod (subtoken, &endptr);
  if (split_high < 0.0 || split_high > 1.0)
  {
    if (errno != 0)             //  error
      error ("Split_high for chronaural had an error.\n");
    else
      split_high = 0.5;
  }
  chronaural1->split_high = split_high;

  subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
  errno = 0;
  double split_beat = strtod (subtoken, &endptr);
  if (split_beat == 0.0)
  {
    if (errno != 0)             //  error
      error ("Split beat for chronaural had an error.\n");
  }
  chronaural1->split_beat = split_beat;

  subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
  errno = 0;
  if (subtoken != NULL && strcmp (subtoken, ">") == 0)
    chronaural1->slide = 1;
}

/*  Initialize all values possible for each voice */

void
init_binaural ()
{
  sndstream *snd1, *snd2;
  stub *stub1 = NULL, *stub2 = NULL;
  void *work1 = NULL, *work2 = NULL;


  snd1 = play_seq;  // root node of play stream
  if (snd1 != NULL)
    work1 = snd1->voices;  // list of voices for this stream
  else
    work1 = NULL;
  snd2 = play_seq->next;  // next node in line
  if (snd2 != NULL)
    work2 = snd2->voices;  // list of voices for next stream node
  else
    work2 = NULL;
  while (snd1 != NULL)
  { 
    while (work1 != NULL)
    { 
      stub1 = (stub *) work1;
      switch (stub1->type)
      { 
        case 1:  // binaural
          { 
            binaural *binaural1 = NULL, *binaural2 = NULL;

            binaural1 = (binaural *) work1;
            binaural1->off1 = binaural1->inc1 = binaural1->off2 = binaural1->inc2 = 0;
            binaural1->amp_off1 = binaural1->amp_inc1 = binaural1->amp_off2 = binaural1->amp_inc2 = 0;
            if (work2 != NULL)
            { 
              stub2 = (stub *) work2;
              if (stub2->type == 1)  // also binaural
              { 
                binaural2 = (binaural *) work2;
                /* Set the pointers to the previous voice's offsets here so it can be used while running.
                   Need to do this even when there is no slide.  Some duplication with below. */
                binaural2->last_off1 = &(binaural1->off1);
                binaural2->last_off2 = &(binaural1->off2);
              } 
            } 
            if (binaural1->slide == 0)
            { 
              binaural1->carr_adj = binaural1->beat_adj = binaural1->amp_adj = 0.0;
              binaural1->amp_beat1_adj = binaural1->amp_beat2_adj = 0.0;
              binaural1->amp_pct1_adj = binaural1->amp_pct2_adj = 0.0;
            } 
            else  // slide to next binaural in stream
            { 
              if (work2 != NULL)
              { 
                if (binaural2 != NULL)  // set above if binaural, NULL means next voice not binaural
                {
                  binaural1->carr_adj = (binaural2->carrier - binaural1->carrier)/ (double) snd1->tot_frames;
                  binaural1->beat_adj = (binaural2->beat - binaural1->beat)/ (double) snd1->tot_frames;
                  binaural1->amp_adj = (binaural2->amp - binaural1->amp)/ (double) snd1->tot_frames;
                  /* Amplitude beats are optional.  If there isn't a match, treat as zero instead */
                  if (binaural2->amp_beat1 > 0.0)
                    binaural1->amp_beat1_adj = (binaural2->amp_beat1 - binaural1->amp_beat1)/ (double) snd1->tot_frames;
                  else  // zero amp_beat1 in next binaural
                    binaural1->amp_beat1_adj = - binaural1->amp_beat1 / (double) snd1->tot_frames;
                  if (binaural2->amp_beat2 > 0.0)
                    binaural1->amp_beat2_adj = (binaural2->amp_beat2 - binaural1->amp_beat2)/ (double) snd1->tot_frames;
                  else  // zero amp_beat2 in next binaural
                    binaural1->amp_beat2_adj = - binaural1->amp_beat2 / (double) snd1->tot_frames;
                  /* Amplitude percents are optional.  If there isn't a match, treat as zero instead */
                  if (binaural2->amp_pct1 > 0.0)
                    binaural1->amp_pct1_adj = (binaural2->amp_pct1 - binaural1->amp_pct1)/ (double) snd1->tot_frames;
                  else  // zero amp_pct1 in next binaural
                    binaural1->amp_pct1_adj = - binaural1->amp_pct1 / (double) snd1->tot_frames;
                  if (binaural2->amp_pct2 > 0.0)
                    binaural1->amp_pct2_adj = (binaural2->amp_pct2 - binaural1->amp_pct2)/ (double) snd1->tot_frames;
                  else  // zero amp_pct2 in next binaural
                    binaural1->amp_pct2_adj = - binaural1->amp_pct2 / (double) snd1->tot_frames;
                } 
                else
                  error ("Slide called for, voice to slide to is not binaural.  Position matters!\n");
              } 
              else
                error ("Slide called for, no next binaural in time sequence!\n");
            }
            break;
          }
        case 2:  // bell
        case 3:  // noise
        case 4:  // stoch
        case 5:  // sample
        case 6:  // repeat
        case 7:  // once
          break;
        case 8:  // chronaural
          {
            chronaural *chronaural1 = NULL, *chronaural2 = NULL;

            chronaural1 = (chronaural *) work1;
            chronaural1->off1 = chronaural1->inc1 = chronaural1->off2 = chronaural1->inc2 = 0;
            if (work2 != NULL)
            { 
              stub2 = (stub *) work2;
              if (stub2->type == 8)  // also chronaural
              { 
                chronaural2 = (chronaural *) work2;
                /* Set the pointers to the previous voice's offsets here so it can be used while running.
                   Need to do this even when there is no slide.  Some duplication with below. */
                chronaural2->last_off1 = &(chronaural1->off1);
                chronaural2->last_off2 = &(chronaural1->off2);
              } 
            } 
            if (chronaural1->slide == 0)
              chronaural1->carr_adj = chronaural1->amp_beat_adj = chronaural1->amp_adj = 0.0;
            else  // slide to next chronaural in stream
            {
              if (work2 != NULL)
              {
                if (chronaural2 != NULL)  // set above if also chronaural, NULL means not chronaural
                {
                  chronaural1->carr_adj = (chronaural2->carrier - chronaural1->carrier)/ (double) snd1->tot_frames;
                  chronaural1->amp_beat_adj = (chronaural2->amp_beat - chronaural1->amp_beat)/ (double) snd1->tot_frames;
                  chronaural1->amp_adj = (chronaural2->amp - chronaural1->amp)/ (double) snd1->tot_frames;
                  /* Set the pointers to the previous voice's offsets here so it can be used while running */
                  chronaural2->last_off1 = &(chronaural1->off1);
                  chronaural2->last_off2 = &(chronaural1->off2);
                }
                else
                  error ("Slide called for, voice to slide to is not chronaural.  Position matters!\n");
              }
              else
                error ("Slide called for, no next chronaural in time sequence!\n");
            }
              /* set up the split logic here as it applies throughout the voice period.
                 don't need to worry about overwriting begin and end splits as they are only used once */
            if (chronaural1->split_begin == -1.0)  // chronaural split start random
            {
              double delta = ( (drand48 ()) * (chronaural1->split_high - chronaural1->split_low));
              chronaural1->split_begin = chronaural1->split_low + delta;      // starting split for chronaural
            }
            chronaural1->split_now = chronaural1->split_begin;      // set working split to begin
            if (chronaural1->split_end == -1.0)  // chronaural split end random
            {
              double delta = ( (drand48 ()) * (chronaural1->split_high - chronaural1->split_low));
              chronaural1->split_end = chronaural1->split_low + delta;      // ending split for chronaural
            }
            if (chronaural1->split_beat == 0.0)  // no split beat
            {
              chronaural1->split_adj = ((chronaural1->split_end - chronaural1->split_begin) 
                                        / (double) snd1->tot_frames);  // adjust per frame
              chronaural1->split_beat_adj = 0.0;  // no split beat, no split beat adjust
            }
            else
            {
              if (chronaural1->split_end < chronaural1->split_begin)  // end always larger for split beat, swap if not
              {
                double split_hold = chronaural1->split_begin;  // swap begin and end
                chronaural1->split_begin = chronaural1->split_end;
                chronaural1->split_end = split_hold;
              }
              chronaural1->split_adj = 0.0;  // don't adjust split when there is a split beat
              double cycle_frames = (int) (out_rate / chronaural1->split_beat);  // frames in a back and forth cycle
              chronaural1->split_beat_adj = ((chronaural1->split_end - chronaural1->split_now) 
                                          / cycle_frames);  // adjust to do that cycle, sign oscillates in generate_frames
            }
            break;
          }
        default:
          break;
      }
      work1 = stub1->next;
      if (work2 != NULL)
      {
        stub2 = (stub *) work2;
        work2 = stub2->next;
      }
    }
    snd1 = snd1->next;
    if (snd1 != NULL)
    {
      work1 = snd1->voices;  // list of voices for this stream
      snd2 = snd1->next;
    }
    else
    {
      work1 = NULL;
      snd2 = NULL;
    }
    if (snd2 != NULL)
      work2 = snd2->voices;  // list of voices for next stream node
    else
      work2 = NULL;
  }
}

//
// Play loop in chunks instead of generating one frame at a time
// This controls the generation of frames, managing totals.
//

void
play_loop ()
{
  struct sndstream *snd1, *snd2;
  int display_count = every*out_rate;  // Print every 5 seconds or so
  double fade_val = 0.0, fade_incr = 0.0;
  long display_frames = 0L;
  int_64 remaining_frames = 0;
 	static double buffer [BUFFER_LEN] ;
 	//static int int_buffer [BUFFER_LEN] ;
 	static double play_buffer [BUFFER_LEN] ;
  int offset = 0, fade_start = 0, fade_length = 0;  // all in frames
	snd_pcm_t *alsa_dev = NULL ;
  int channels = 2;  // always output stereo
  slice *sound_slice;  // holds arguments for alsa_play_*
  point_in_time *snd_point;  // holds arguments for status_t
  pthread_t pth_play, pth_status;  // threads for play and status
  pthread_attr_t attr_play, attr_status;  // attributes for play and status

      /* open alsa default via libsndfile */
  alsa_dev = alsa_open (alsa_dev, channels, (unsigned) out_rate, SF_FALSE); 
      /* set up the slice structure that will be passed to alsa_play_* */
  sound_slice = (slice *) Alloc (sizeof (slice) * 1);
  sound_slice->alsa_dev = alsa_dev;  // sound device
  sound_slice->sndfile = NULL;  // file pointer
  sound_slice->buffer = play_buffer; // buffer to play, change if type changed
  sound_slice->frames = BUFFER_LEN/channels; // number of frames in buffer
  sound_slice->channels = channels; // number of channels in a frame
      /* set up the thread attributes that will be used for each thread invocation of alsa_play_* */
  pthread_attr_destroy (&attr_play);  // destroy attributes
  pthread_attr_init (&attr_play);  // initialize attributes
  pthread_attr_setdetachstate (&attr_play, PTHREAD_CREATE_DETACHED);  // run detached
      /* set up the file device in the point_in_time structure that will be passed to status */
  snd_point = (point_in_time *) Alloc (sizeof (point_in_time) * 1);
  snd_point->fp = stderr; // file device to write to
      /* set up the thread attributes that will be used for each thread invocation of status */
  pthread_attr_destroy (&attr_status);  // destroy attributes
  pthread_attr_init (&attr_status);  // initialize attributes
  pthread_attr_setdetachstate (&attr_status, PTHREAD_CREATE_DETACHED);  // run detached
  snd1 = play_seq;  // start of voice sequence linked list
  if (snd1 != NULL)
  {
    //status (snd1, stderr);
    snd_point->snd1 = snd1;  // sound stream to status
    pthread_create (&pth_status, &attr_status, (void *) &status_t, (void *) snd_point);
  }
  while (1)
  {
      /* set the sound stream in the point_in_time structure that will be passed to status */
    snd_point->snd1 = snd1;  // sound stream to status
    if (snd1->fade == 1)  // fade in
    {
      fade_val = 0.0;  // start at zero amplitude
      fade_incr = 1.0/snd1->tot_frames;  // adjust each frame
    }
    else if (snd1->fade == 2)  // fade out
    {
      fade_val = 1.0;  // start at one amplitude
      fade_incr = -1.0/snd1->tot_frames;  // adjust each frame
    }
    while (snd1->cur_frames < snd1->tot_frames)  // for whole time period
    {
      remaining_frames = ((snd1->tot_frames - snd1->cur_frames) / fast_mult);
      if (remaining_frames >= (BUFFER_LEN/channels))
      { // more than a buffer full to go
        fade_start = 0;  // if period has fade, start fading at this offset
        fade_length = BUFFER_LEN/channels;  // end fade at this offset
          // generate a full buffer
        offset = generate_frames (snd1, buffer, offset, (BUFFER_LEN/channels));
      }
      else if (remaining_frames < (BUFFER_LEN/channels))
      { // less than a buffer for this time period
        fade_start = 0;
        fade_length = (int) remaining_frames;
          // generate a partial buffer
        offset = generate_frames (snd1, buffer, offset, (int) remaining_frames);
      }
      if (snd1->fade)  // there is a fade in this time period
      {
        int ii;
        for (ii=channels * fade_start; ii < channels * fade_length; ii+= channels)
        {  // fade one frame at a time
          buffer[ii] *= fade_val;
          buffer[ii+1] *= fade_val;
          fade_val += fade_incr * fast_mult;
        }
      }
      display_frames += (fade_length * fast_mult);  // adjust display frames
      if (display_frames >= display_count)  // time to display?
      {
        pthread_mutex_lock (&mtx_status);  // block until previous status operation complete
          /* this create is non blocking, continue creating frames to play */
        pthread_create (&pth_status, &attr_status, (void *) &status_t, (void *) snd_point);
        pthread_mutex_unlock (&mtx_status);   // release mutex so status_t can lock it
        //status (snd1, stderr);
        display_frames = 0L;
      }
      snd1->cur_frames += (fade_length * fast_mult);  // adjust frames so far in this sound stream
      if (!opt_d)
      {
        sound_slice->frames = offset; // number of frames in buffer
        pthread_mutex_lock (&mtx_play);  // block until previous play operation complete
        memcpy (play_buffer, buffer, sizeof(buffer));  // copy frames to play
            /* this create is non blocking, continue creating frames to play */
        //pthread_create (&pth_play, &attr_play, (void *) &alsa_write, (void *) sound_slice);
        pthread_mutex_unlock (&mtx_play);  // release mutex so alsa_write can lock it
        alsa_write_double (alsa_dev, play_buffer, offset, channels) ;
      }
      offset = 0;
    }
    snd2 = snd1->next;  // move to next time period
    snd1 = snd2;
    if (snd1 == NULL)
      break;  // finished all time periods, out of the loop
  }
  snd_pcm_drain (alsa_dev) ;  // shutdown the alsa card
  snd_pcm_close (alsa_dev) ;
}

//
// Save loop
// Needs to be fixed for new style
//

void
save_loop ()
{
  struct sndstream *snd1, *snd2;
  int display_count = every*out_rate;  // Print every 5 seconds or so
  double fade_val = 0.0, fade_incr = 0.0;
  long display_frames = 0L;
  int_64 remaining_frames = 0;
 	static double buffer [BUFFER_LEN] ;
 	//static int int_buffer [BUFFER_LEN] ;
 	static double write_buffer [BUFFER_LEN] ;
  int offset = 0, fade_start = 0, fade_length = 0;  // all in frames
  SNDFILE * sndfile = NULL;
  SF_INFO sfinfo;
  int channels = 2;  // always output stereo
  slice *sound_slice;  // holds arguments for write_file
  point_in_time *snd_point;  // holds arguments for status_t
  pthread_t pth_write, pth_status;  // threads for file and status
  pthread_attr_t attr_write, attr_status;  // attributes for file and status

  sfinfo.samplerate = out_rate;  // sample frames per second
  sfinfo.channels = 2;  // always write stereo
  sfinfo.format = outfile_format | bit_accuracy;  // e.g. flac and 32 bit
  int checkval = sf_format_check (&sfinfo);
  sndfile = sf_open (out_filename, SFM_WRITE, &sfinfo);
  if (!sndfile)
    error ("Couldn't open write file %s\n", out_filename);
      /* set up the slice structure that will be passed to write_file in thread */
  sound_slice = (slice *) Alloc (sizeof (slice) * 1);
  sound_slice->alsa_dev = NULL;  // sound device pointer
  sound_slice->sndfile = sndfile;  // file pointer
  sound_slice->buffer = write_buffer; // buffer to write, change if type changed
  sound_slice->frames = BUFFER_LEN/channels; // number of frames in buffer
  sound_slice->channels = channels; // number of channels in a frame
      /* set up the thread attributes that will be used for each thread invocation of write_file */
  pthread_attr_destroy (&attr_write);  // destroy attributes
  pthread_attr_init (&attr_write);  // initialize attributes
  pthread_attr_setdetachstate (&attr_write, PTHREAD_CREATE_DETACHED);  // run detached
      /* set up the file device in the point_in_time structure that will be passed to status */
  snd_point = (point_in_time *) Alloc (sizeof (point_in_time) * 1);
  snd_point->fp = stderr; // file device to write to
      /* set up the thread attributes that will be used for each thread invocation of status */
  pthread_attr_destroy (&attr_status);  // destroy attributes
  pthread_attr_init (&attr_status);  // initialize attributes
  pthread_attr_setdetachstate (&attr_status, PTHREAD_CREATE_DETACHED);  // run detached
  snd1 = play_seq;  // start of voice sequence linked list
  if (snd1 != NULL)
  {
    //status (snd1, stderr);
    snd_point->snd1 = snd1;  // sound stream to status
    pthread_create (&pth_status, &attr_status, (void *) &status_t, (void *) snd_point);
  }
  while (1)
  {
      /* set the sound stream in the point_in_time structure that will be passed to status */
    snd_point->snd1 = snd1;  // sound stream to status
    if (snd1->fade == 1)  // fade in
    {
      fade_val = 0.0;  // start at zero amplitude
      fade_incr = 1.0/snd1->tot_frames;  // adjust each frame
    }
    else if (snd1->fade == 2)  // fade out
    {
      fade_val = 1.0;  // start at one amplitude
      fade_incr = -1.0/snd1->tot_frames;  // adjust each frame
    }
    while (snd1->cur_frames < snd1->tot_frames)  // for whole time period
    {
      remaining_frames = ((snd1->tot_frames - snd1->cur_frames) / fast_mult);
      if (remaining_frames >= (BUFFER_LEN/channels))
      { // more than a buffer full to go
        fade_start = 0;  // if period has fade, start fading at this offset
        fade_length = BUFFER_LEN/channels;  // end fade at this offset
          // generate a full buffer
        offset = generate_frames (snd1, buffer, offset, (BUFFER_LEN/channels));
      }
      else if (remaining_frames < (BUFFER_LEN/channels))
      { // less than a buffer for this time period
        fade_start = 0;
        fade_length = (int) remaining_frames;
          // generate a partial buffer
        offset = generate_frames (snd1, buffer, offset, (int) remaining_frames);
      }
      if (snd1->fade)  // there is a fade in this time period
      {
        int ii;
        for (ii=channels * fade_start; ii < channels * fade_length; ii+= channels)
        {  // fade one frame at a time
          buffer[ii] *= fade_val;
          buffer[ii+1] *= fade_val;
          fade_val += fade_incr * fast_mult;
        }
      }
      display_frames += (fade_length * fast_mult);  // adjust display frames
      if (display_frames >= display_count)  // time to display?
      {
        pthread_mutex_lock (&mtx_status);  // block until previous status operation complete
          /* this create is non blocking, continue creating frames to write */
        pthread_create (&pth_status, &attr_status, (void *) &status_t, (void *) snd_point);
        pthread_mutex_unlock (&mtx_status);   // release mutex so status_t can lock it
        //status (snd1, stderr);
        display_frames = 0L;
      }
      snd1->cur_frames += (fade_length * fast_mult);  // adjust frames so far in this sound stream
      if (!opt_d)
      {
        sound_slice->frames = offset; // number of frames in buffer
        pthread_mutex_lock (&mtx_write);  // block until previous write operation complete
        memcpy (write_buffer, buffer, sizeof(buffer));  // copy frames to write
            /* this create is non blocking, continue creating frames to write */
        //pthread_create (&pth_write, &attr_write, (void *) &file_write, (void *) sound_slice);
        pthread_mutex_unlock (&mtx_write);  // release mutex so file_write can lock it
        /* writing from a double */
        offset = sf_writef_double (sndfile, write_buffer, offset);
      }
      offset = 0;
    }
    snd2 = snd1->next;  // move to next time period
    snd1 = snd2;
    if (snd1 == NULL)
      break;  // finished all time periods, out of the loop
  }
  sf_close (sndfile);
}

/* Generate the number of frames of data requested,
   combining each voice in current period */
int
generate_frames (struct sndstream *snd1, double *out_buffer, int offset, int frame_count)
{
  int ii;
  int channels = 2;  // always output stereo
  stub *stub1;
  void *this, *next;

  for (ii= channels * offset; ii < channels * frame_count; ii+= channels)
  {  // zero out the sound to be in the buffer
    out_buffer[ii] = out_buffer[ii+1] = 0.0;
  }
  this = snd1->voices;
  while (this != NULL)
  {
    stub1 = (stub *) this;  // assign void pointer as stub, handler, has type
    switch (stub1->type)
    {
      case 0:
        break;
      case 1:                // Binaural tones
        {
          double freq1, freq2;
          double amp1, amp2;
          binaural *binaural1;

          binaural1 = (binaural *) this;  // reassign void pointer as binaural struct

          /* if start of the voice, set starting offset to be last offset of previous voice */
          if (binaural1->first_pass)
          {
            binaural1->first_pass = 0;  // now active
            if (binaural1->last_off1 != NULL)  // there *is* a previous offset to use
              binaural1->off1 = *binaural1->last_off1;  // to eliminate crackle from discontinuity in wave
            if (binaural1->last_off2 != NULL)  // there *is* a previous offset to use
              binaural1->off2 = *binaural1->last_off2;
          }
          for (ii= channels * offset; ii < channels * frame_count; ii+= channels)
          {
            freq1 = binaural1->carrier + binaural1->beat / 2;
            freq2 = binaural1->carrier - binaural1->beat / 2;
            if (opt_c)  // compensate
            {
              amp1 = (binaural1->amp * amp_comp (freq1));
              amp2 = (binaural1->amp * amp_comp (freq2));
            }
            else
              amp1 = amp2 = binaural1->amp;
            /* perform the amplitude variation adjustment if required */
            if (binaural1->amp_beat1 > 0.0)
            {
              binaural1->amp_inc1 = (int) round(binaural1->amp_beat1*2);
              binaural1->amp_off1 += binaural1->amp_inc1;
              binaural1->amp_off1 = binaural1->amp_off1 % (out_rate * 2);
              amp1 += ((amp1 * binaural1->amp_pct1) * sin_table[binaural1->amp_off1]);
            }
            if (binaural1->amp_beat2 > 0.0)
            {
              binaural1->amp_inc2 = (int) round(binaural1->amp_beat2*2);
              binaural1->amp_off2 += binaural1->amp_inc2;
              binaural1->amp_off2 = binaural1->amp_off2 % (out_rate * 2);
              amp2 += ((amp2 * binaural1->amp_pct2) * sin_table[binaural1->amp_off2]);
            }
            binaural1->inc1 = (int) round(freq1*2);  // (freq1 / out_rate) * (out_rate * 2));
            binaural1->off1 += binaural1->inc1;
            binaural1->off1 = binaural1->off1 % (out_rate * 2);
            out_buffer[ii] += (amp1 * sin_table[binaural1->off1]);
            binaural1->inc2 = (int) round(freq2*2);  // (freq2 / out_rate) * (out_rate * 2));
            binaural1->off2 += binaural1->inc2;
            binaural1->off2 = binaural1->off2 % (out_rate * 2);
            out_buffer[ii+1] += (amp2 * sin_table[binaural1->off2]);
            if (binaural1->slide)
            { /* adjust values for next pass only if this binaural is sliding */
              binaural1->carrier += (binaural1->carr_adj * fast_mult);
              binaural1->amp += (binaural1->amp_adj * fast_mult);
              binaural1->beat += (binaural1->beat_adj * fast_mult);
              binaural1->amp_beat1 += (binaural1->amp_beat1_adj * fast_mult);
              binaural1->amp_beat2 += (binaural1->amp_beat2_adj * fast_mult);
              binaural1->amp_pct1 += (binaural1->amp_pct1_adj * fast_mult);
              binaural1->amp_pct2 += (binaural1->amp_pct2_adj * fast_mult);
            }
          }
        }
        break;
      case 2:                // Bell
        {
          bell *bell1;
          double split_end = 0.0;  // hold the ending split while creating voice

          bell1 = (bell *) this;  // reassign void pointer as bell struct
          for (ii= channels * offset; ii < channels * frame_count; ii+= channels)
          {
            bell1->sofar += fast_mult;
            if (bell1->sofar >= bell1->next_play)
            {                     // time to ring
              bell1->sofar = 0;
              if (bell1->repeat_max == bell1->repeat_min)
              {
                bell1->next_play = bell1->repeat_min;      // fixed period
              }
              else
              {
                long delta =
                  (long) (( drand48 ()) * (bell1->repeat_max - bell1->repeat_min));
//                  (long) ( (rand () / (RAND_MAX + 1.0)) *
//                           (bell1->repeat_max - bell1->repeat_min));
                bell1->next_play = bell1->repeat_min + delta;      // frames to next bell
              }
              if (bell1->length_max == bell1->length_min)
              {                   // fixed ring time
                bell1->ring = bell1->length_min;
              }
              else
              {
                long delta =
                  (long) ( (drand48 ()) * (bell1->length_max - bell1->length_min));
                bell1->ring = bell1->length_min + delta;      // frames to ring
              }
              if (bell1->amp_max == bell1->amp_min)
              {                   // fixed amp
                bell1->amp = bell1->amp_min;
              }
              else
              {
                double delta = ( (drand48 ()) * (bell1->amp_max - bell1->amp_min));
                bell1->amp = bell1->amp_min + delta;       // beginning amplitude of tone
              }
              if (opt_c)  // compensate, could be done in setup for bell, less obvious
                bell1->amp *= amp_comp (bell1->carrier);
              if (bell1->behave == 1)   // linear amp_adj to zero
                bell1->amp_adj = - (bell1->amp / bell1->ring);
              else if (bell1->behave == 2)      // amp_adj to half
                bell1->amp_adj = - (bell1->amp * .50) / bell1->ring;
              else if (bell1->behave == 3)
                bell1->amp_adj = 0.0;     // no change
              else if (bell1->behave == 4)      // linear enhance to 1.10
                bell1->amp_adj = (bell1->amp * .10) / bell1->ring;
              else if (bell1->behave == 5)      // enhance to 1.25, maybe make bell1 exponential decay
                //bell1->amp_adj = (bell1->amp * .25) / bell1->ring;
                bell1->amp_adj = - sqrt(bell1->amp) / bell1->ring;
              if (bell1->split_begin == -1.0)  // bell split start
              {
                double delta = ( (drand48 ()) * (bell1->split_high - bell1->split_low));
                bell1->split_now = bell1->split_low + delta;      // starting split for bell
              }
              else
                bell1->split_now = bell1->split_begin;      // fixed starting split
              if (bell1->split_end == -1.0)  // bell split end
              {
                double delta = ( (drand48 ()) * (bell1->split_high - bell1->split_low));
                split_end = bell1->split_low + delta;      // ending split for bell
              }
              else
                split_end = bell1->split_end;      // fixed ending split
              bell1->split_adj = (split_end - bell1->split_now) / bell1->ring;  // adjust per frame
            }
            if (bell1->ring > 0L)
            {
              bell1->inc1 = (int) round( bell1->carrier * 2. * fast_mult);
              //bell1->inc1 = (int) round(( (bell1->carrier * (out_rate * 2)) / out_rate) * fast_mult);
              bell1->off1 += bell1->inc1;
              bell1->off1 = bell1->off1 % (out_rate * 2);
              out_buffer[ii] += bell1->split_now * bell1->amp * sin_table[bell1->off1];
              out_buffer[ii+1] += (1.0 - bell1->split_now) * bell1->amp * sin_table[bell1->off1];
              if (bell1->behave == 5)  // exponential decay
                bell1->amp = (pow((sqrt(bell1->amp) + (bell1->amp_adj * fast_mult)), 2.0));
              else
                bell1->amp += (bell1->amp_adj * fast_mult);  // linear adjustment
              if (bell1->amp < 0.0)
                bell1->amp = 0.0;
              bell1->split_now += (bell1->split_adj * fast_mult);
              bell1->ring -= fast_mult;
            }
          }
        }
        break;
      case 3:                // Noise
        {
          noise *noise1;
          double split_end = 0.0;  // hold the ending split while creating voice

          noise1 = (noise *) this;  // reassign void pointer as noise struct
          for (ii= channels * offset; ii < channels * frame_count; ii+= channels)
          {
            noise1->sofar += fast_mult;
            if (noise1->sofar >= noise1->next_play)
            {                     // time to play
              noise1->sofar = 0;
              /* First determine the play length for this tone.
                 Has to be first as the next play depends on it. */
              if (noise1->length_max == noise1->length_min)
              {                   // fixed play time
                noise1->play = noise1->length_min;
              }
              else
              {
                long delta = (long) ( (drand48 ()) * (noise1->length_max - noise1->length_min));
                noise1->play = noise1->length_min + delta;      // frames to play
              }
              if (noise1->repeat_max == noise1->repeat_min)
              {
                // fixed period between noise plays, after current noise finishes
                noise1->next_play = noise1->repeat_min + noise1->play;   
              }
              else
              {
                long delta = (long) ( (drand48 ()) * (noise1->repeat_max - noise1->repeat_min));
                // frames to next tone after current finishes playing
                noise1->next_play = noise1->repeat_min + delta + noise1->play;      
              }
              if (noise1->carrier_max == noise1->carrier_min)
              {                   // fixed carrier
                noise1->carrier = noise1->carrier_min;
              }
              else
              {
                double delta = ( (drand48 ()) * (noise1->carrier_max - noise1->carrier_min));
                noise1->carrier = noise1->carrier_min + delta;       // frequency of tone
              }
              if (noise1->amp_max == noise1->amp_min)
              {                   // fixed amp
                noise1->amp = noise1->amp_min;
              }
              else
              {
                double delta = ( (drand48 ()) * (noise1->amp_max - noise1->amp_min));
                noise1->amp = noise1->amp_min + delta;       // beginning amplitude of tone
              }
              if (opt_c)  // compensate
                noise1->amp *= amp_comp (noise1->carrier);
              if (noise1->behave_low == noise1->behave_high)
              {                   // fixed decay behavior
                noise1->behave = noise1->behave_low;
              }
              else // choose decay style for noise1 tone
              {
                int diff = (noise1->behave_high - noise1->behave_low) + 1;
                noise1->behave = noise1->behave_low + (int) (rand () % diff);
              }
              if (noise1->behave == 1)   // linear reduce to .50
                noise1->amp_adj = - (noise1->amp * .50) / noise1->play;
              else if (noise1->behave == 2)      // linear reduce to .90
                noise1->amp_adj = - (noise1->amp * .10) / noise1->play;
              else if (noise1->behave == 3)
                noise1->amp_adj = 0.0;     // no change
              else if (noise1->behave == 4)      // linear enhance to 1.10
                noise1->amp_adj = (noise1->amp * .10) / noise1->play;
              else if (noise1->behave == 5)      // linear enhance to 1.50
                noise1->amp_adj = (noise1->amp * .50) / noise1->play;
                /* assign directly to split_now to preserve -1 in split begin */
              if (noise1->split_begin == -1.0)  // noise split start
              {
                double delta = ( (drand48 ()) * (noise1->split_high - noise1->split_low));
                noise1->split_now = noise1->split_low + delta;      // starting split for tone
              }
              else
                noise1->split_now = noise1->split_begin;      // fixed starting split
                /* assign to local split_end to preserve -1 in split end */
              if (noise1->split_end == -1.0)  // noise split end
              {
                double delta = ( (drand48 ()) * (noise1->split_high - noise1->split_low));
                split_end = noise1->split_low + delta;      // ending split for tone
              }
              else
                split_end = noise1->split_end;      // fixed ending split
              noise1->split_adj = (split_end - noise1->split_now) / noise1->play;  // adjust per frame
            }
            if (noise1->play > 0)  // noise is active
            {
              //noise1->inc1 = (int) (( (noise1->carrier * (out_rate * 2)) / out_rate) * fast_mult);
              noise1->inc1 = (int) round( noise1->carrier * 2. * fast_mult);
              noise1->off1 += noise1->inc1;
              noise1->off1 = noise1->off1 % (out_rate * 2);
              out_buffer[ii] += noise1->split_now * noise1->amp * sin_table[noise1->off1];
              out_buffer[ii+1] += (1.0 - noise1->split_now) * noise1->amp * sin_table[noise1->off1];
              noise1->amp += (noise1->amp_adj * fast_mult);
              noise1->split_now += (noise1->split_adj * fast_mult);
              noise1->play -= fast_mult;
            }
          }
        }
        break;
      case 4:                // Random file play
        {
          stoch *stoch1;
          double split_end = 0.0;  // hold the ending split while creating voice

          stoch1 = (stoch *) this;  // reassign void pointer as stoch struct
          for (ii= channels * offset; ii < channels * frame_count; ii+= channels)
          {
            stoch1->sofar += fast_mult;
            if (stoch1->sofar >= stoch1->next_play)
            {                     // time to play
              stoch1->sofar = 0;
              stoch1->off1 = 0;
              stoch1->play = stoch1->frames; // fixed play time
              if (stoch1->repeat_max == stoch1->repeat_min)
              {
                stoch1->next_play = stoch1->repeat_min + stoch1->play; // fixed period
              }
              else
              {
                long delta = (long) ( (drand48 ()) * (stoch1->repeat_max - stoch1->repeat_min));
                // frames to next play after current play ends
                stoch1->next_play = stoch1->repeat_min + delta + stoch1->play;
              }
              if (stoch1->amp_max == stoch1->amp_min)
              {                   // fixed amp
                stoch1->amp = stoch1->amp_min;
              }
              else
              {
                double delta = ( (drand48 ()) * (stoch1->amp_max - stoch1->amp_min));
                stoch1->amp = stoch1->amp_min + delta;       // beginning amplitude of tone
              }
              if (stoch1->split_begin == -1.0)  // stoch split start
              {
                double delta = ( (drand48 ()) * (stoch1->split_high - stoch1->split_low));
                stoch1->split_now = stoch1->split_low + delta;      // starting split
              }
              else
                stoch1->split_now = stoch1->split_begin;      // fixed starting split
                
              if (stoch1->split_end == -1.0)  // stoch split end
              {
                double delta = ( (drand48 ()) * (stoch1->split_high - stoch1->split_low));
                split_end = stoch1->split_low + delta;      // ending split
              }
              else
                split_end = stoch1->split_end;      // fixed ending split
                
              stoch1->split_adj = (split_end - stoch1->split_now) / stoch1->play;  // adjust per frame
            }
            if (stoch1->play > 0L)  // stoch is active
            {
                  // if channels not 1 or 2, off1 out of synch with out_buffer[ii] and out_buffer[ii+1]
              stoch1->off1 += (stoch1->channels * fast_mult);
              stoch1->off1 %= stoch1->frames;  
              if (stoch1->mono == 0)  // stereo
              {
                out_buffer[ii] += (stoch1->split_now * stoch1->amp
                        * (((double) *(stoch1->sound + stoch1->off1)) * stoch1->scale));
                out_buffer[ii+1] += ((1.0 - stoch1->split_now) * stoch1->amp
                        * (double) ((*(stoch1->sound + stoch1->off1 + 1)) * stoch1->scale));
              }
              else if (stoch1->mono == 1)  // mono, repeat left as right channel
              {
                out_buffer[ii] += (stoch1->split_now * stoch1->amp
                        * (((double) *(stoch1->sound + stoch1->off1)) * stoch1->scale));
                out_buffer[ii+1] += ((1.0 - stoch1->split_now) * stoch1->amp
                        * (((double) *(stoch1->sound + stoch1->off1)) * stoch1->scale));
              }
              else if (stoch1->mono == 2)  // mono, repeat right as left channel
              {
                out_buffer[ii] += (stoch1->split_now * stoch1->amp
                        * (((double) *(stoch1->sound + stoch1->off1 + 1)) * stoch1->scale));
                out_buffer[ii+1] += ((1.0 - stoch1->split_now) * stoch1->amp
                        * (((double) *(stoch1->sound + stoch1->off1 + 1)) * stoch1->scale));
              }
              stoch1->split_now += (stoch1->split_adj * fast_mult);
                  // if channels not 1 or 2, play out of synch with out_buffer[ii] and out_buffer[ii+1]
              stoch1->play -= fast_mult;
            }
          }
        }
        break;
      case 5:                // Sample file play
        {
          sample *sample1;
          double split_end = 0.0;  // hold the ending split while creating voice

          sample1 = (sample *) this;  // reassign void pointer as sample struct
          for (ii= channels * offset; ii < channels * frame_count; ii+= channels)
          {
            if (sample1->play <= 0)  // done playing, time to play another sample
            {     
                  // frame start for next play
              sample1->off1 = (long) ((drand48 ()) * sample1->frames);
              sample1->play = sample1->size; // fixed play time/frames
              if (sample1->amp_max == sample1->amp_min)
              {                   // fixed amp
                sample1->amp = sample1->amp_min;
              }
              else
              {
                double delta = ( (drand48 ()) * (sample1->amp_max - sample1->amp_min));
                sample1->amp = sample1->amp_min + delta;       // beginning amplitude of tone
              }
              if (sample1->split_begin == -1.0)  // random split start
              {
                double delta = ( (drand48 ()) * (sample1->split_high - sample1->split_low));
                sample1->split_now = sample1->split_low + delta;      // starting split for sample
              }
              else
                sample1->split_now = sample1->split_begin;      // fixed starting split
              if (sample1->split_end == -1.0)  // random split end
              {
                double delta = ( (drand48 ()) * (sample1->split_high - sample1->split_low));
                split_end = sample1->split_low + delta;      // ending split
              }
              else
                split_end = sample1->split_end;      // fixed ending split
                
              sample1->split_adj = (split_end - sample1->split_now) / sample1->play;  // adjust per frame
            }
            if (sample1->play > 0L)  // sample is active
            {
                  // if channels not 1 or 2, off1 out of synch with out_buffer[ii] and out_buffer[ii+1]
              sample1->off1 += (sample1->channels * fast_mult);
              sample1->off1 %= sample1->frames;  
              if (sample1->mono == 0)  // stereo
              {
                out_buffer[ii] += (sample1->split_now * sample1->amp
                        * (((double) *(sample1->sound + sample1->off1)) * sample1->scale));
                out_buffer[ii+1] += ((1.0 - sample1->split_now) * sample1->amp
                        * (double) ((*(sample1->sound + sample1->off1 + 1)) * sample1->scale));
              }
              else if (sample1->mono == 1)  // mono, repeat left as right channel
              {
                out_buffer[ii] += (sample1->split_now * sample1->amp
                        * (((double) *(sample1->sound + sample1->off1)) * sample1->scale));
                out_buffer[ii+1] += ((1.0 - sample1->split_now) * sample1->amp
                        * (((double) *(sample1->sound + sample1->off1)) * sample1->scale));
              }
              else if (sample1->mono == 2)  // mono, repeat right as left channel
              {
                out_buffer[ii] += (sample1->split_now * sample1->amp
                        * (((double) *(sample1->sound + sample1->off1 + 1)) * sample1->scale));
                out_buffer[ii+1] += ((1.0 - sample1->split_now) * sample1->amp
                        * (((double) *(sample1->sound + sample1->off1 + 1)) * sample1->scale));
              }
              sample1->split_now += (sample1->split_adj * fast_mult);
                  // if channels not 1 or 2, play out of synch with out_buffer[ii] and out_buffer[ii+1]
              sample1->play -= fast_mult;
            }
          }
        }
        break;
      case 6:                // Repeat/loop file play
        {
          repeat *repeat1;
          double split_end = 0.0;  // hold the ending split while creating voice

          repeat1 = (repeat *) this;  // reassign void pointer as repeat struct
          for (ii= channels * offset; ii < channels * frame_count; ii+= channels)
          {
            if (repeat1->play <= 0)
            {                     // time to play another repeat
              repeat1->off1 = 0;
              repeat1->play = repeat1->frames; // fixed play time
              if (repeat1->amp_max == repeat1->amp_min)
              {                   // fixed amp
                repeat1->amp = repeat1->amp_min;
              }
              else
              {
                double delta = ( (drand48 ()) * (repeat1->amp_max - repeat1->amp_min));
                repeat1->amp = repeat1->amp_min + delta;       // beginning amplitude of tone
              }
              if (repeat1->split_begin == -1.0)  // random split start
              {
                double delta = ( (drand48 ()) * (repeat1->split_high - repeat1->split_low));
                repeat1->split_now = repeat1->split_low + delta;      // starting split for repeat
              }
              else
                repeat1->split_now = repeat1->split_begin;      // fixed starting split
              if (repeat1->split_end == -1.0)  // random split end
              {
                double delta = ( (drand48 ()) * (repeat1->split_high - repeat1->split_low));
                split_end = repeat1->split_low + delta;      // ending split for repeat
              }
              else
                split_end = repeat1->split_end;      // fixed ending split
              repeat1->split_adj = (split_end - repeat1->split_now) / repeat1->play;  // adjust per frame
            }
            if (repeat1->play > 0L)  // repeat is active
            {
                  // if channels not 1 or 2, off1 out of synch with out_buffer[ii] and out_buffer[ii+1]
              repeat1->off1 += (repeat1->channels * fast_mult);
              repeat1->off1 %= repeat1->frames;  
              if (repeat1->mono == 0)  // stereo
              {
                out_buffer[ii] += (repeat1->split_now * repeat1->amp
                        * (((double) *(repeat1->sound + repeat1->off1)) * repeat1->scale));
                out_buffer[ii+1] += ((1.0 - repeat1->split_now) * repeat1->amp
                        * (double) ((*(repeat1->sound + repeat1->off1 + 1)) * repeat1->scale));
              }
              else if (repeat1->mono == 1)  // mono, repeat left as right channel
              {
                out_buffer[ii] += (repeat1->split_now * repeat1->amp
                        * (((double) *(repeat1->sound + repeat1->off1)) * repeat1->scale));
                out_buffer[ii+1] += ((1.0 - repeat1->split_now) * repeat1->amp
                        * (((double) *(repeat1->sound + repeat1->off1)) * repeat1->scale));
              }
              else if (repeat1->mono == 2)  // mono, repeat right as left channel
              {
                out_buffer[ii] += (repeat1->split_now * repeat1->amp
                        * (((double) *(repeat1->sound + repeat1->off1 + 1)) * repeat1->scale));
                out_buffer[ii+1] += ((1.0 - repeat1->split_now) * repeat1->amp
                        * (((double) *(repeat1->sound + repeat1->off1 + 1)) * repeat1->scale));
              }
              repeat1->split_now += (repeat1->split_adj * fast_mult);
                  // if channels not 1 or 2, play out of synch with out_buffer[ii] and out_buffer[ii+1]
              repeat1->play -= fast_mult;
            }
          }
        }
        break;
      case 7:                // Once file play
        {
          once *once1;
          double split_end = 0.0;  // hold the ending split while creating voice

          once1 = (once *) this;  // reassign void pointer as once struct
          for (ii= channels * offset; ii < channels * frame_count; ii+= channels)
          {
            once1->sofar += fast_mult;
            if (once1->sofar >= once1->next_play)
            {                     // time to play
              once1->sofar = 0;
              once1->off1 = 0;  // start at beginning of buffer
              once1->play = once1->frames; // fixed play time
              once1->next_play = 0x7fffffffffffffffLL; // next play max so won't play again
              if (once1->amp_max == once1->amp_min)
              {                   // fixed amp
                once1->amp = once1->amp_min;
              }
              else
              {
                double delta = ( (drand48 ()) * (once1->amp_max - once1->amp_min));
                once1->amp = once1->amp_min + delta;       // beginning amplitude of tone
              }
              if (once1->split_begin == -1.0)  // once split start
              {
                double delta = ( (drand48 ()) * (once1->split_high - once1->split_low));
                once1->split_now = once1->split_low + delta;      // starting split
              }
              else
                once1->split_now = once1->split_begin;      // fixed starting split
                
              if (once1->split_end == -1.0)  // once split end
              {
                double delta = ( (drand48 ()) * (once1->split_high - once1->split_low));
                split_end = once1->split_low + delta;      // ending split
              }
              else
                split_end = once1->split_end;      // fixed ending split
                
              once1->split_adj = (split_end - once1->split_now) / once1->play;  // adjust per frame
            }
            if (once1->play > 0L)  // once is active
            {
                  // if channels not 1 or 2, off1 out of synch with out_buffer[ii] and out_buffer[ii+1]
              once1->off1 += (once1->channels * fast_mult);
              once1->off1 %= once1->frames;  
                // assumes only 1 or two channels, default to two if not one
              if (once1->mono == 0)  // stereo
              {
                out_buffer[ii] += (once1->split_now * once1->amp
                        * (((double) *(once1->sound + once1->off1)) * once1->scale));
                out_buffer[ii+1] += ((1.0 - once1->split_now) * once1->amp
                        * (double) ((*(once1->sound + once1->off1 + 1)) * once1->scale));
              }
              else if (once1->mono == 1)  // mono, repeat left as right channel
              {
                out_buffer[ii] += (once1->split_now * once1->amp
                        * (((double) *(once1->sound + once1->off1)) * once1->scale));
                out_buffer[ii+1] += ((1.0 - once1->split_now) * once1->amp
                        * (((double) *(once1->sound + once1->off1)) * once1->scale));
              }
              else if (once1->mono == 2)  // mono, repeat right as left channel
              {
                out_buffer[ii] += (once1->split_now * once1->amp
                        * (((double) *(once1->sound + once1->off1 + 1)) * once1->scale));
                out_buffer[ii+1] += ((1.0 - once1->split_now) * once1->amp
                        * (((double) *(once1->sound + once1->off1 + 1)) * once1->scale));
              }
              once1->split_now += (once1->split_adj * fast_mult);
                  // if channels not 1 or 2, play out of synch with out_buffer[ii] and out_buffer[ii+1]
              once1->play -= fast_mult;
            }
          }
        }
        break;
      case 8:                // Chronaural tones
        {
          double freq1, sinval;
          double amp1;
          chronaural *chronaural1;

          chronaural1 = (chronaural *) this;  // reassign void pointer as chronaural struct

          if (chronaural1->first_pass)
          {
            chronaural1->first_pass = 0;  // now active
            if (chronaural1->last_off1 != NULL)  // there *is* a previous offset to use
              chronaural1->off1 = *chronaural1->last_off1;  // to eliminate crackle from discontinuity in wave
            if (chronaural1->last_off2 != NULL)  // there *is* a previous offset to use
              chronaural1->off2 = *chronaural1->last_off2;
          }
          for (ii= channels * offset; ii < channels * frame_count; ii+= channels)
          {
            chronaural1->inc2 = (int) round( chronaural1->amp_beat * 2. * fast_mult);  //inc to next sin value
            chronaural1->off2 += chronaural1->inc2;  // offset for beat frequency into sin table
            chronaural1->off2 = chronaural1->off2 % (out_rate * 2);  // mod to wrap offset
            sinval = sin_table [chronaural1->off2];  // sin val at current amp_beat point
            if (sinval > chronaural1->amp_fraction)  // time to play, only on positive sine
            {
              freq1 = chronaural1->carrier;
              if (opt_c)  // compensate
              {
                amp1 = (chronaural1->amp * amp_comp (freq1));
              }
              else
                amp1 = chronaural1->amp;
              chronaural1->inc1 = (int) round(freq1*2);  // (freq1 / out_rate) * (out_rate * 2));
              chronaural1->off1 += chronaural1->inc1;
              chronaural1->off1 = chronaural1->off1 % (out_rate * 2);
              if (chronaural1->amp_behave == 1)  // sin wave, adjust by sin value
              {
                out_buffer[ii] += (chronaural1->split_now * sinval * amp1 * sin_table[chronaural1->off1]);
                out_buffer[ii+1] += ((1.0 - chronaural1->split_now) * sinval * amp1 * sin_table[chronaural1->off1]);
              }
              else if (chronaural1->amp_behave == 2)      // square wave, full volume
              {
                out_buffer[ii] += (chronaural1->split_now * amp1 * sin_table[chronaural1->off1]);
                out_buffer[ii+1] += ((1.0 - chronaural1->split_now) * amp1 * sin_table[chronaural1->off1]);
              }
              else if (chronaural1->amp_behave == 3)  // dirac delta approximation
              {
                double filter = pow(sinval, 5.); // quint the sin to make pseudo dirac
                out_buffer[ii] += (chronaural1->split_now * filter * amp1 * sin_table[chronaural1->off1]);
                out_buffer[ii+1] += ((1.0 - chronaural1->split_now) * filter * amp1 * sin_table[chronaural1->off1]);
              }
            }
            if (chronaural1->split_beat == 0.0)  // no split beat, adjust split towards split_end
            {
              chronaural1->split_now += (chronaural1->split_adj * fast_mult);
              if (chronaural1->split_now < 0.0)
                chronaural1->split_now = 0.0;
              else if (chronaural1->split_now > 1.0)
                chronaural1->split_now = 1.0;
            }
            else // split beat so no split adjust, split beat adjust instead, oscillates between begin and end
            {
              chronaural1->split_now += chronaural1->split_beat_adj * fast_mult;
                /* assumes split_end > split_begin, this is done in init_binaural */
              if (chronaural1->split_now > chronaural1->split_end)  // larger than end
              {
                chronaural1->split_now = chronaural1->split_end;
                chronaural1->split_beat_adj *= -1.;  // swap direction
              }
              else if (chronaural1->split_now < chronaural1->split_begin)  // smaller than begin
              {
                chronaural1->split_now = chronaural1->split_begin;
                chronaural1->split_beat_adj *= -1.;  // swap direction
              }
            }  
            chronaural1->carrier += (chronaural1->carr_adj * fast_mult);  // tone to sound if time
            chronaural1->amp += (chronaural1->amp_adj * fast_mult);  // amplitude to sound at
            if (chronaural1->amp < 0.0)  // no negative amplitudes
              chronaural1->amp = 0.0;
            chronaural1->amp_beat += (chronaural1->amp_beat_adj * fast_mult);  // beat of the amplitude
          }
        }
        break;
      default:               // do nothing if not recognized
        ;
    }
    next = stub1->next;  // move to next voice
    this = next;
  }
  return frame_count;
}

//
// Round a double to nearest integer
//
inline double round (double num)
{
  return (num - floor(num)) < 0.5 ? floor (num) : ceil (num);
}

//
// Update a status line
// Threaded version
//

void *
status_t (void *call_parms)
{
  void *this, *next;
  stub *stub1;
  static sndstream *prev = NULL;

  status_t_retval = 0;
  if (opt_q)  // quiet
    return &status_t_retval;

  pthread_mutex_lock (&mtx_status);  // prevent main from calling while processing

  /* extract calling parameters from passed in structure */
  point_in_time *snd_point = (point_in_time *) call_parms;
  sndstream * snd1 = snd_point->snd1;
  FILE *fp = snd_point->fp;

  fprint_time (fp);  // add the time
  this = snd1->voices;  // point to first voice
  while (this != NULL)
  {
    if (snd1 == prev)  // already seen
      fprint_voice (fp, this);  // add each voice
    else  // first time
      fprint_voice_all (fp, this);  // add each voice
    stub1 = (stub *) this;
    next = stub1->next;
    this = next;
  }
  prev = snd1;
  fflush (fp);
  pthread_mutex_unlock (&mtx_status);  // allow main to call again
  return &status_t_retval;
}

int
fprint_time (FILE *fp)
{
  int char_count = 0;
  time_t time_now, utc_secs;
  struct tm *broken_time;

  time_now = time(&utc_secs);  // seconds since Jan 1 1970 UTC
  broken_time = localtime(&time_now);  // seconds broken into components
  char_count = fprintf (fp, "%02d:%02d:%02d\n", 
                  broken_time->tm_hour, broken_time->tm_min, broken_time->tm_sec);
  return char_count;
}

/* Print all the information from a voice to a file pointer */
int
fprint_voice_all (FILE *fp, void *this)
{
  int char_count = 0;
  stub *stub1;

  stub1 = (stub *) this;
  switch (stub1->type)
  {
    case 0:
      ;
      break;
    case 1:  // binaural
      {
        binaural *binaural1;

        binaural1 = (binaural *) this;
        char_count += fprintf (fp, "   bin %.3f %+.3f", binaural1->carrier, binaural1->beat);
        char_count += fprintf (fp, " %.3f", AMP_DA (binaural1->amp));
        char_count += fprintf (fp, " %.3f %.3f", binaural1->amp_beat1, binaural1->amp_beat2);
        char_count += fprintf (fp, " %.3f %.3f", AMP_DA (binaural1->amp_pct1), AMP_DA (binaural1->amp_pct2));
        char_count += fprintf (fp, " %d %d %d %d", binaural1->inc1, binaural1->off1, binaural1->inc2, binaural1->off2);
        char_count += fprintf (fp, " %d %d %d %d", 
                                   binaural1->amp_inc1, binaural1->amp_off1, binaural1->amp_inc2, binaural1->amp_off2);
        char_count += fprintf (fp, " %.3e %.3e %.3e", binaural1->carr_adj, binaural1->beat_adj, binaural1->amp_adj);
        char_count += fprintf (fp, " %.3e %.3e", binaural1->amp_beat1_adj, binaural1->amp_beat2_adj);
        char_count += fprintf (fp, " %.3e %.3e", binaural1->amp_pct1_adj, binaural1->amp_pct2_adj);
        char_count += fprintf (fp, " %d\n", binaural1->slide);
      }
      break;
    case 2:  // bell
      {
        bell *bell1;

        bell1 = (bell *) this;
        char_count += fprintf (fp, "   bell %.3f %.3e %.3f", 
                        bell1->carrier, AMP_DA (bell1->amp), bell1->split_now );
        char_count += fprintf (fp, " %.3f %.3f %.3f %.3f",
                        bell1->split_begin, bell1->split_end, bell1->split_low, bell1->split_high);
        char_count += fprintf (fp, " %.3f %.3f", 
                        AMP_DA (bell1->amp_min), AMP_DA (bell1->amp_max));
        char_count += fprintf (fp, " %lld %lld %lld %lld",
                        bell1->length_min, bell1->length_max, bell1->repeat_min, bell1->repeat_max);
        char_count += fprintf (fp, " %d %d %d %lld %lld %lld",
                        bell1->behave, bell1->inc1, bell1->off1, bell1->next_play,
                        bell1->sofar, bell1->ring);
        char_count += fprintf (fp, " %.3e %.3e\n",
                        bell1->amp_adj, bell1->split_adj);
      }
      break;
    case 3:  // noise
      {
        noise *noise1;

        noise1 = (noise *) this;
        char_count += fprintf (fp, "   noise %.3f %.3e %.3f", 
                        noise1->carrier, AMP_DA (noise1->amp), noise1->split_now );
        char_count += fprintf (fp, " %.3f %.3f %.3f %.3f",
                        noise1->split_begin, noise1->split_end, noise1->split_low, noise1->split_high);
        char_count += fprintf (fp, " %.3f %.3f", 
                        noise1->carrier_min, noise1->carrier_max);
        char_count += fprintf (fp, " %.3f %.3f", 
                        AMP_DA (noise1->amp_min), AMP_DA (noise1->amp_max));
        char_count += fprintf (fp, " %lld %lld %lld %lld ",
                        noise1->length_min, noise1->length_max, noise1->repeat_min, noise1->repeat_max);
        char_count += fprintf (fp, " %d %d %d %lld %lld %lld",
                        noise1->behave, noise1->behave_low, noise1->behave_high, noise1->next_play,
                        noise1->sofar, noise1->play);
        char_count += fprintf (fp, " %.3e %.3e\n",
                        noise1->amp_adj, noise1->split_adj);
      }
      break;
    case 4:  // random
      {
        stoch *stoch1;

        stoch1 = (stoch *) this;
        char_count += fprintf (fp, "   stoch %lld %d",
                        stoch1->frames, stoch1->channels);
        char_count += fprintf (fp, " %.3f %.3f", 
                        AMP_DA (stoch1->amp), stoch1->split_now );
        char_count += fprintf (fp, " %.3f %.3f %.3f %.3f",
                        stoch1->split_begin, stoch1->split_end, stoch1->split_low, stoch1->split_high);
        char_count += fprintf (fp, " %.3f %.3f", 
                        AMP_DA (stoch1->amp_min), AMP_DA (stoch1->amp_max));
        char_count += fprintf (fp, " %lld %lld",
                        stoch1->repeat_min, stoch1->repeat_max);
        char_count += fprintf (fp, " %lld %lld %lld %lld",
                        stoch1->next_play, stoch1->sofar, stoch1->off1, stoch1->play);
        char_count += fprintf (fp, " %.3e %d\n",
                        stoch1->split_adj, stoch1->mono);
      }
      break;
    case 5:  // sample
      {
        sample *sample1;

        sample1 = (sample *) this;
        char_count += fprintf (fp, "   sample %lld %d",
                        sample1->frames, sample1->channels);
        char_count += fprintf (fp, " %.3f %.3f", 
                        AMP_DA (sample1->amp), sample1->split_now );
        char_count += fprintf (fp, " %.3f %.3f %.3f %.3f",
                        sample1->split_begin, sample1->split_end, sample1->split_low, sample1->split_high);
        char_count += fprintf (fp, " %.3f %.3f", 
                        AMP_DA (sample1->amp_min), AMP_DA (sample1->amp_max));
        char_count += fprintf (fp, " %lld %lld %lld %lld",
                        sample1->size, sample1->sofar, sample1->off1, sample1->play);
        char_count += fprintf (fp, " %.3e %d\n",
                        sample1->split_adj, sample1->mono);
      }
      break;
    case 6:  // repeat
      {
        repeat *repeat1;

        repeat1 = (repeat *) this;
        char_count += fprintf (fp, "   repeat %lld %d",
                        repeat1->frames, repeat1->channels);
        char_count += fprintf (fp, " %.3f %.3f", 
                        AMP_DA (repeat1->amp), repeat1->split_now );
        char_count += fprintf (fp, " %.3f %.3f %.3f %.3f",
                        repeat1->split_begin, repeat1->split_end, repeat1->split_low, repeat1->split_high);
        char_count += fprintf (fp, " %.3f %.3f", 
                        AMP_DA (repeat1->amp_min), AMP_DA (repeat1->amp_max));
        char_count += fprintf (fp, " %lld %lld %lld",
                        repeat1->sofar, repeat1->off1, repeat1->play);
        char_count += fprintf (fp, " %.3e %d\n",
                        repeat1->split_adj, repeat1->mono);
      }
      break;
    case 7:  // once
      {
        once *once1;

        once1 = (once *) this;
        char_count += fprintf (fp, "   once %lld %d",
                        once1->frames, once1->channels);
        char_count += fprintf (fp, " %.3f %.3f", 
                        AMP_DA (once1->amp), once1->split_now );
        char_count += fprintf (fp, " %.3f %.3f %.3f %.3f",
                        once1->split_begin, once1->split_end, once1->split_low, once1->split_high);
        char_count += fprintf (fp, " %.3f %.3f", 
                        AMP_DA (once1->amp_min), AMP_DA (once1->amp_max));
        char_count += fprintf (fp, " %lld",
                        once1->play_when);
        char_count += fprintf (fp, " %lld %lld %lld %lld",
                        once1->next_play, once1->sofar, once1->off1, once1->play);
        char_count += fprintf (fp, " %.3e %d\n",
                        once1->split_adj, once1->mono);
      }
      break;
    case 8:  // chronaural
      {
        chronaural *chronaural1;

        chronaural1 = (chronaural *) this;
        char_count += fprintf (fp, "   chron %.3f", chronaural1->carrier);
        char_count += fprintf (fp, " %.3f", AMP_DA (chronaural1->amp));
        char_count += fprintf (fp, " %.3e %.3e", chronaural1->amp_beat, chronaural1->amp_fraction);
        char_count += fprintf (fp, " %d", chronaural1->amp_behave);
        char_count += fprintf (fp, " %d %d", chronaural1->inc1, chronaural1->off1);
        char_count += fprintf (fp, " %d %d", chronaural1->inc2, chronaural1->off2);
        char_count += fprintf (fp, " %.3e %.3e %.3e", chronaural1->carr_adj, chronaural1->amp_beat_adj, chronaural1->amp_adj);
        char_count += fprintf (fp, " %.3f", chronaural1->split_now );
        char_count += fprintf (fp, " %.3f %.3f %.3f %.3f",
                        chronaural1->split_begin, chronaural1->split_end, chronaural1->split_low, chronaural1->split_high);
        char_count += fprintf (fp, " %.3e", chronaural1->split_beat);
        char_count += fprintf (fp, " %.3e %.3e",
                        chronaural1->split_beat_adj, chronaural1->split_adj);
        char_count += fprintf (fp, " %d\n", chronaural1->slide);
      }
      break;
    default:  // not known, do nothing
      ;
  }
  return char_count;
}

/* Print selected information from a voice to a file pointer */
int
fprint_voice (FILE *fp, void *this)
{
  int char_count = 0;
  stub *stub1;

  stub1 = (stub *) this;
  switch (stub1->type)
  {
    case 0:
      ;
      break;
    case 1:  // binaural
      {
        double freq1, freq2;
        double amp1, amp2;
        binaural *binaural1;

        binaural1 = (binaural *) this;  // reassign void pointer as binaural struct
          /* use last calculated values instead of calculating new ones */
        freq1 = binaural1->carrier + binaural1->beat / 2;
        freq2 = binaural1->carrier - binaural1->beat / 2;
        if (opt_c)  // compensate
        {
          amp1 = (binaural1->amp * amp_comp (freq1));
          amp2 = (binaural1->amp * amp_comp (freq2));
        }
        else
          amp1 = amp2 = binaural1->amp;
          /* perform the amplitude variation adjustment if required */
        if (binaural1->amp_beat1 > 0.0)
          amp1 += ((amp1 * binaural1->amp_pct1) * sin_table[binaural1->amp_off1]);
        if (binaural1->amp_beat2 > 0.0)
          amp2 += ((amp2 * binaural1->amp_pct2) * sin_table[binaural1->amp_off2]);
        char_count = fprintf (fp, "   bin %.3f   %+.3f   %.3f   %.3f\n", 
                      binaural1->carrier, binaural1->beat, AMP_DA (amp1), AMP_DA (amp2));
      }
      break;
    case 2:  // bell
      {
        bell *bell1;

        bell1 = (bell *) this;
        char_count = fprintf (fp, "   bell %.3f   %.3e   %.3f\n", 
                      bell1->carrier,  AMP_DA (bell1->amp), bell1->split_now );
        break;
      }
    case 3:  // noise
      {
        noise *noise1;

        noise1 = (noise *) this;
        char_count = fprintf (fp, "   noise %.3f   %.3e   %.3f\n", 
                      noise1->carrier, AMP_DA (noise1->amp * amp_comp (noise1->carrier)), noise1->split_now );
        break;
      }
    case 4:  // random
      {
        stoch *stoch1;

        stoch1 = (stoch *) this;
        char_count = fprintf (fp, "   stoch %lld   %lld   %.3f   %.3f\n", 
                      stoch1->off1, stoch1->play, AMP_DA (stoch1->amp), stoch1->split_now );
        break;
      }
    case 5:  // sample
      {
        sample *sample1;

        sample1 = (sample *) this;
        char_count = fprintf (fp, "   sample %lld   %lld   %.3f   %.3f\n", 
                      sample1->off1, sample1->play, AMP_DA (sample1->amp), sample1->split_now );
        break;
      }
    case 6:  // repeat
      {
        repeat *repeat1;

        repeat1 = (repeat *) this;
        char_count = fprintf (fp, "   repeat %lld   %lld   %.3f   %.3f\n", 
                      repeat1->off1, repeat1->play, AMP_DA (repeat1->amp), repeat1->split_now );
        break;
      }
    case 7:  // once
      {
        once *once1;

        once1 = (once *) this;
        char_count = fprintf (fp, "   once %lld   %lld   %.3f   %.3f\n", 
                      once1->off1, once1->play, AMP_DA (once1->amp), once1->split_now );
        break;
      }
    case 8:  // chronaural
      {
        chronaural *chronaural1;

        chronaural1 = (chronaural *) this;
        char_count += fprintf (fp, "   chron %.3f", chronaural1->carrier);
        char_count += fprintf (fp, " %.3f", AMP_DA (chronaural1->amp * amp_comp (chronaural1->carrier)));
        char_count += fprintf (fp, " %.3e", chronaural1->amp_beat);
        char_count += fprintf (fp, " %.3f\n", chronaural1->split_now );
        break;
      }
    default:  // not known, do nothing
      ;
  }
  return char_count;
}

//
// Update a status line
//

void
status (struct sndstream * snd1, FILE * fp)
{
  void *this, *next;
  char buffer[8192];
  char *p = buffer, *p0, *p1;
  static sndstream *prev = NULL;
  stub *stub1;

  if (opt_q)  // quiet
    return;

  memset (buffer, 0x00, 8192);  // zero the buffer

  p0 = p;                       // Start of line
  sprintTime (&p);  // add the time
  this = snd1->voices;  // point to first voice
  while (this != NULL)
  {
    if (snd1 == prev)  // already seen
      sprintVoice (&p, this);  // add each voice
    else  // first time
      sprintVoiceAll (&p, this);  // add each voice
    stub1 = (stub *) this;
    next = stub1->next;
    this = next;
  }
  prev = snd1;
  p1 = p;                       // End of line

  fprintf (fp, "%s\n", buffer);
  fflush (fp);
}

void
sprintTime (char **p)
{
  time_t time_now, utc_secs;
  struct tm *broken_time;

  time_now = time(&utc_secs);  // seconds since Jan 1 1970 UTC
#ifdef NOTDEFINED
  char time_str[30];
  ctime_r (&time_now, time_str);
  *p += sprintf (*p, "%s", time_str);
#endif
  broken_time = localtime(&time_now);  // seconds broken into components
  *p += sprintf (*p, "%02d:%02d:%02d\n", 
                  broken_time->tm_hour, broken_time->tm_min, broken_time->tm_sec);
}

/* Print all the information from a voice to a string */
void
sprintVoiceAll (char **p, void *this)
{
  stub *stub1;

  stub1 = (stub *) this;
  switch (stub1->type)
  {
    case 0:
      ;
      break;
    case 1:  // binaural
      {
        binaural *binaural1;

        binaural1 = (binaural *) this;
        *p += sprintf (*p, "   bin %.3f %+.3f %.3f", binaural1->carrier, binaural1->beat, AMP_DA (binaural1->amp));
        *p += sprintf (*p, " %.3f %.3f", binaural1->amp_beat1, binaural1->amp_beat2);
        *p += sprintf (*p, " %.3f %.3f", AMP_DA (binaural1->amp_pct1), AMP_DA (binaural1->amp_pct2));
        *p += sprintf (*p, " %d %d %d %d", binaural1->inc1, binaural1->off1, binaural1->inc2, binaural1->off2);
        *p += sprintf (*p, " %d %d %d %d", binaural1->amp_inc1, binaural1->amp_off1, binaural1->amp_inc2, binaural1->amp_off2);
        *p += sprintf (*p, " %.3e% .3e %.3e", binaural1->carr_adj, binaural1->beat_adj, binaural1->amp_adj);
        *p += sprintf (*p, " %.3e %.3e", binaural1->amp_beat1_adj, binaural1->amp_beat2_adj);
        *p += sprintf (*p, " %.3e %.3e", binaural1->amp_pct1_adj, binaural1->amp_pct2_adj);
        *p += sprintf (*p, " %d\n", binaural1->slide);
      }
      break;
    case 2:  // bell
      {
        bell *bell1;

        bell1 = (bell *) this;
        *p += sprintf (*p, "   bell %.3f %.3e %.3f", 
                        bell1->carrier, AMP_DA (bell1->amp), bell1->split_now );
        *p += sprintf (*p, " %.3f %.3f %.3f %.3f",
                        bell1->split_begin, bell1->split_end, bell1->split_low, bell1->split_high);
        *p += sprintf (*p, " %.3f %.3f", 
                        AMP_DA (bell1->amp_min), AMP_DA (bell1->amp_max));
        *p += sprintf (*p, " %lld %lld %lld %lld",
                        bell1->length_min, bell1->length_max, bell1->repeat_min, bell1->repeat_max);
        *p += sprintf (*p, " %d %d %d %lld %lld %lld",
                        bell1->behave, bell1->inc1, bell1->off1, bell1->next_play,
                        bell1->sofar, bell1->ring);
        *p += sprintf (*p, " %.3e %.3e\n",
                        bell1->amp_adj, bell1->split_adj);
        break;
      }
    case 3:  // noise
      {
        noise *noise1;

        noise1 = (noise *) this;
        *p += sprintf (*p, "   noise %.3f %.3e %.3f", 
                        noise1->carrier, AMP_DA (noise1->amp), noise1->split_now );
        *p += sprintf (*p, " %.3f %.3f %.3f %.3f",
                        noise1->split_begin, noise1->split_end, noise1->split_low, noise1->split_high);
        *p += sprintf (*p, " %.3f %.3f", 
                        noise1->carrier_min, noise1->carrier_max);
        *p += sprintf (*p, " %.3f %.3f", 
                        AMP_DA (noise1->amp_min), AMP_DA (noise1->amp_max));
        *p += sprintf (*p, " %lld %lld %lld %lld ",
                        noise1->length_min, noise1->length_max, noise1->repeat_min, noise1->repeat_max);
        *p += sprintf (*p, " %d %d %d %lld %lld %lld",
                        noise1->behave, noise1->behave_low, noise1->behave_high, noise1->next_play,
                        noise1->sofar, noise1->play);
        *p += sprintf (*p, " %.3e %.3e\n",
                        noise1->amp_adj, noise1->split_adj);
        break;
      }
    case 4:  // random
      {
        stoch *stoch1;

        stoch1 = (stoch *) this;
        *p += sprintf (*p, "   stoch %lld %d",
                        stoch1->frames, stoch1->channels);
        *p += sprintf (*p, " %.3f %.3f", 
                        AMP_DA (stoch1->amp), stoch1->split_now );
        *p += sprintf (*p, " %.3f %.3f %.3f %.3f",
                        stoch1->split_begin, stoch1->split_end, stoch1->split_low, stoch1->split_high);
        *p += sprintf (*p, " %.3f %.3f", 
                        AMP_DA (stoch1->amp_min), AMP_DA (stoch1->amp_max));
        *p += sprintf (*p, " %lld %lld",
                        stoch1->repeat_min, stoch1->repeat_max);
        *p += sprintf (*p, " %lld %lld %lld %lld",
                        stoch1->next_play, stoch1->sofar, stoch1->off1, stoch1->play);
        *p += sprintf (*p, " %.3e %d\n",
                        stoch1->split_adj, stoch1->mono);
        break;
      }
    case 5:  // sample
      {
        sample *sample1;

        sample1 = (sample *) this;
        *p += sprintf (*p, "   sample %lld %d",
                        sample1->frames, sample1->channels);
        *p += sprintf (*p, " %.3f %.3f", 
                        AMP_DA (sample1->amp), sample1->split_now );
        *p += sprintf (*p, " %.3f %.3f %.3f %.3f",
                        sample1->split_begin, sample1->split_end, sample1->split_low, sample1->split_high);
        *p += sprintf (*p, " %.3f %.3f", 
                        AMP_DA (sample1->amp_min), AMP_DA (sample1->amp_max));
        *p += sprintf (*p, " %lld %lld %lld %lld",
                        sample1->size, sample1->sofar, sample1->off1, sample1->play);
        *p += sprintf (*p, " %.3e %d\n",
                        sample1->split_adj, sample1->mono);
        break;
      }
    case 6:  // repeat
      {
        repeat *repeat1;

        repeat1 = (repeat *) this;
        *p += sprintf (*p, "   repeat %lld %d",
                        repeat1->frames, repeat1->channels);
        *p += sprintf (*p, " %.3f %.3f", 
                        AMP_DA (repeat1->amp), repeat1->split_now );
        *p += sprintf (*p, " %.3f %.3f %.3f %.3f",
                        repeat1->split_begin, repeat1->split_end, repeat1->split_low, repeat1->split_high);
        *p += sprintf (*p, " %.3f %.3f", 
                        AMP_DA (repeat1->amp_min), AMP_DA (repeat1->amp_max));
        *p += sprintf (*p, " %lld %lld %lld",
                        repeat1->sofar, repeat1->off1, repeat1->play);
        *p += sprintf (*p, " %.3e, %d\n",
                        repeat1->split_adj, repeat1->mono);
        break;
      }
    case 7:  // once
      {
        once *once1;

        once1 = (once *) this;
        *p += sprintf (*p, "   once %lld %d",
                        once1->frames, once1->channels);
        *p += sprintf (*p, " %.3f %.3f", 
                        AMP_DA (once1->amp), once1->split_now );
        *p += sprintf (*p, " %.3f %.3f %.3f %.3f",
                        once1->split_begin, once1->split_end, once1->split_low, once1->split_high);
        *p += sprintf (*p, " %.3f %.3f", 
                        AMP_DA (once1->amp_min), AMP_DA (once1->amp_max));
        *p += sprintf (*p, " %lld",
                        once1->play_when);
        *p += sprintf (*p, " %lld %lld %lld %lld",
                        once1->next_play, once1->sofar, once1->off1, once1->play);
        *p += sprintf (*p, " %.3e %d\n",
                        once1->split_adj, once1->mono);
        break;
      }
    case 8:  // chronaural
      {
        chronaural *chronaural1;

        chronaural1 = (chronaural *) this;
        *p += sprintf (*p, "   chron %.3f", chronaural1->carrier);
        *p += sprintf (*p, " %.3f", AMP_DA (chronaural1->amp));
        *p += sprintf (*p, " %.3e %.3e", chronaural1->amp_beat, chronaural1->amp_fraction);
        *p += sprintf (*p, " %d", chronaural1->amp_behave);
        *p += sprintf (*p, " %d %d", chronaural1->inc1, chronaural1->off1);
        *p += sprintf (*p, " %d %d", chronaural1->inc2, chronaural1->off2);
        *p += sprintf (*p, " %.3e %.3e %.3e", chronaural1->carr_adj, chronaural1->amp_beat_adj, chronaural1->amp_adj);
        *p += sprintf (*p, " %.3f", chronaural1->split_now );
        *p += sprintf (*p, " %.3f %.3f %.3f %.3f",
                        chronaural1->split_begin, chronaural1->split_end, chronaural1->split_low, chronaural1->split_high);
        *p += sprintf (*p, " %.3e", chronaural1->split_beat);
        *p += sprintf (*p, " %.3e %.3e",
                        chronaural1->split_beat_adj, chronaural1->split_adj);
        *p += sprintf (*p, " %d\n", chronaural1->slide);
        break;
      }
    default:  // not known, do nothing
      ;
  }
}

/* Print selected information from a voice to a string */
void
sprintVoice (char **p, void *this)
{
  stub *stub1;

  stub1 = (stub *) this;
  switch (stub1->type)
  {
    case 0:
      ;
      break;
    case 1:  // binaural
      {
        binaural *binaural1;

        binaural1 = (binaural *) this;
        *p += sprintf (*p, "   bin %.3f   %+.3f   %.3f\n", 
                      binaural1->carrier, binaural1->beat, AMP_DA (binaural1->amp * amp_comp (binaural1->carrier)));
      }
      break;
    case 2:  // bell
      {
        bell *bell1;

        bell1 = (bell *) this;
        *p += sprintf (*p, "   bell %.3f   %.3e   %.3f\n", 
                      bell1->carrier, AMP_DA (bell1->amp), bell1->split_now );
        break;
      }
    case 3:  // noise
      {
        noise *noise1;

        noise1 = (noise *) this;
        *p += sprintf (*p, "   noise %.3f   %.3e   %.3f\n", 
                      noise1->carrier, AMP_DA (noise1->amp * amp_comp (noise1->carrier)), noise1->split_now );
        break;
      }
    case 4:  // random
      {
        stoch *stoch1;

        stoch1 = (stoch *) this;
        *p += sprintf (*p, "   stoch %lld   %lld   %.3f   %.3f\n", 
                      stoch1->off1, stoch1->play, AMP_DA (stoch1->amp), stoch1->split_now );
        break;
      }
    case 5:  // sample
      {
        sample *sample1;

        sample1 = (sample *) this;
        *p += sprintf (*p, "   sample %lld   %lld   %.3f   %.3f\n", 
                      sample1->off1, sample1->play, AMP_DA (sample1->amp), sample1->split_now );
        break;
      }
    case 6:  // repeat
      {
        repeat *repeat1;

        repeat1 = (repeat *) this;
        *p += sprintf (*p, "   repeat %lld   %lld   %.3f   %.3f\n", 
                      repeat1->off1, repeat1->play, AMP_DA (repeat1->amp), repeat1->split_now );
        break;
      }
    case 7:  // once
      {
        once *once1;

        once1 = (once *) this;
        *p += sprintf (*p, "   once %lld   %lld   %.3f   %.3f\n", 
                      once1->off1, once1->play, AMP_DA (once1->amp), once1->split_now );
        break;
      }
    case 8:  // chronaural
      {
        chronaural *chronaural1;

        chronaural1 = (chronaural *) this;
        *p += sprintf (*p, "   chron %.3f", chronaural1->carrier);
        *p += sprintf (*p, " %.3f", AMP_DA (chronaural1->amp * amp_comp (chronaural1->carrier)));
        *p += sprintf (*p, " %.3e", chronaural1->amp_beat);
        *p += sprintf (*p, " %.3f\n", chronaural1->split_now );
        break;
      }
    default:  // not known, do nothing
      ;
  }
}


void
error (char *fmt, ...)
{
  va_list ap;

  va_start (ap, fmt);
  vfprintf (stderr, fmt, ap);
  fprintf (stderr, "\n");
#ifdef EXIT_KEY
  fprintf (stderr, "Press <RETURN> to continue: ");
  fflush (stderr);
  getchar ();
#endif
  exit (1);
}

void
debug (char *fmt, ...)
{
  va_list ap;

  va_start (ap, fmt);
  vfprintf (stderr, fmt, ap);
  fprintf (stderr, "\n");
}

void
warn (char *fmt, ...)
{
  va_list ap;

  va_start (ap, fmt);
  vfprintf (stderr, fmt, ap);
  fprintf (stderr, "\n");
}

void *
Alloc (size_t len)
{
  void *p = calloc (1, len);

  if (!p)
    error ("Out of memory in request for %u", len);
  return p;
}

char *
StrDup (char *str)
{
  char *rv = strdup (str);

  if (!rv)
    error ("Out of memory");
  return rv;
}

/*------------------------------------------------------------------------------
**	Linux alsa functions for playing a sound.
*/

static snd_pcm_t *
alsa_open (snd_pcm_t *alsa_dev, int channels, unsigned samplerate, int realtime)
{	
  const char * device = "default" ;
  // const char * device = "analog" ;
  //const char * device = "plughw:0,0" ;
  unsigned val;
  unsigned long lval;
  int dir = 0;
	snd_pcm_hw_params_t *hw_params ;
	snd_pcm_uframes_t buffer_size, xfer_align, start_threshold ;
	snd_pcm_uframes_t alsa_period_size, alsa_buffer_frames ;
	snd_pcm_sw_params_t *sw_params ;

	int err ;

	if (realtime)
	{	alsa_period_size = 256 ;
		alsa_buffer_frames = 3 * alsa_period_size ;
		}
	else
	{	alsa_period_size = 1024 ;
		alsa_buffer_frames = 8 * alsa_period_size ;
		} ;

	if ((err = snd_pcm_open (&alsa_dev, device, SND_PCM_STREAM_PLAYBACK, 0)) < 0)
	{	fprintf (stderr, "cannot open audio device \"%s\" (%s)\n", device, snd_strerror (err)) ;
		goto catch_error ;
		} ;

	//snd_pcm_nonblock (alsa_dev, 0) ;  // 0 means block, 1 means nonblock

	if ((err = snd_pcm_hw_params_malloc (&hw_params)) < 0)
	{	fprintf (stderr, "cannot allocate hardware parameter structure (%s)\n", snd_strerror (err)) ;
		goto catch_error ;
		} ;

	if ((err = snd_pcm_hw_params_any (alsa_dev, hw_params)) < 0)
	{	fprintf (stderr, "cannot initialize hardware parameter structure (%s)\n", snd_strerror (err)) ;
		goto catch_error ;
		} ;

  // check parameters for the card
  snd_pcm_hw_params_get_channels_min (hw_params, &val);
  fprintf (stderr, "Minimum channels (%u)\n", val);
  snd_pcm_hw_params_get_channels_max (hw_params, &val);
  fprintf (stderr, "Maximum channels (%u)\n", val);
  snd_pcm_hw_params_get_rate_min (hw_params, &val, &dir);
  fprintf (stderr, "Minimum rate (%u)  Direction = %d\n", val, dir);
  snd_pcm_hw_params_get_rate_max (hw_params, &val, &dir);
  fprintf (stderr, "Maximum rate (%u)  Direction = %d\n", val, dir);
  snd_pcm_hw_params_get_period_time_min (hw_params, &val, &dir);
  fprintf (stderr, "Minimum period_time (%u)  Direction = %d\n", val, dir);
  snd_pcm_hw_params_get_period_time_max (hw_params, &val, &dir);
  fprintf (stderr, "Maximum period_time (%u)  Direction = %d\n", val, dir);
  snd_pcm_hw_params_get_period_size_min (hw_params, &lval, &dir);
  fprintf (stderr, "Minimum period_size (%lu)  Direction = %d\n", lval, dir);
  snd_pcm_hw_params_get_period_size_max (hw_params, &lval, &dir);
  fprintf (stderr, "Maximum period_size (%lu)  Direction = %d\n", lval, dir);
  snd_pcm_hw_params_get_periods_min (hw_params, &val, &dir);
  fprintf (stderr, "Minimum periods (%u)  Direction = %d\n", val, dir);
  snd_pcm_hw_params_get_periods_max (hw_params, &val, &dir);
  fprintf (stderr, "Maximum periods (%u)  Direction = %d\n", val, dir);
  snd_pcm_hw_params_get_buffer_time_min (hw_params, &val, &dir);
  fprintf (stderr, "Minimum buffer_time (%u)  Direction = %d\n", val, dir);
  snd_pcm_hw_params_get_buffer_time_max (hw_params, &val, &dir);
  fprintf (stderr, "Maximum buffer_time (%u)  Direction = %d\n", val, dir);
  snd_pcm_hw_params_get_buffer_size_min (hw_params, &lval);
  fprintf (stderr, "Minimum buffer_size (%lu)\n", lval);
  snd_pcm_hw_params_get_buffer_size_max (hw_params, &lval);
  fprintf (stderr, "Maximum buffer_size (%lu)\n", lval);
  snd_pcm_hw_params_get_tick_time_min (hw_params, &val, &dir);
  fprintf (stderr, "Minimum tick_time (%u)  Direction = %d\n", val, dir);
  snd_pcm_hw_params_get_tick_time_max (hw_params, &val, &dir);
  fprintf (stderr, "Maximum tick_time (%u)  Direction = %d\n", val, dir);

	if ((err = snd_pcm_hw_params_set_access (alsa_dev, hw_params, SND_PCM_ACCESS_RW_INTERLEAVED)) < 0)
	{	fprintf (stderr, "cannot set access type (%s)\n", snd_strerror (err)) ;
		goto catch_error ;
		} ;

	if ((err = snd_pcm_hw_params_set_format (alsa_dev, hw_params, SND_PCM_FORMAT_FLOAT64)) < 0)
	//if ((err = snd_pcm_hw_params_set_format (alsa_dev, hw_params, SND_PCM_FORMAT_S32_LE)) < 0)
	{	fprintf (stderr, "cannot set sample format (%s)\n", snd_strerror (err)) ;
		goto catch_error ;
		} ;

	if ((err = snd_pcm_hw_params_set_rate_near (alsa_dev, hw_params, &samplerate, 0)) < 0)
	{	fprintf (stderr, "cannot set sample rate (%s)\n", snd_strerror (err)) ;
		goto catch_error ;
		} ;

	if ((err = snd_pcm_hw_params_set_channels (alsa_dev, hw_params, channels)) < 0)
	{	fprintf (stderr, "cannot set channel count (%s)\n", snd_strerror (err)) ;
		goto catch_error ;
		} ;

	if ((err = snd_pcm_hw_params_set_buffer_size_near (alsa_dev, hw_params, &alsa_buffer_frames)) < 0)
	{	fprintf (stderr, "cannot set buffer size (%s)\n", snd_strerror (err)) ;
		goto catch_error ;
		} ;

	if ((err = snd_pcm_hw_params_set_period_size_near (alsa_dev, hw_params, &alsa_period_size, 0)) < 0)
	{	fprintf (stderr, "cannot set period size (%s)\n", snd_strerror (err)) ;
		goto catch_error ;
		} ;

	if ((err = snd_pcm_hw_params (alsa_dev, hw_params)) < 0)
	{	fprintf (stderr, "cannot set parameters (%s)\n", snd_strerror (err)) ;
		goto catch_error ;
		} ;

	/* extra check: if we have only one period, this code won't work */
	snd_pcm_hw_params_get_period_size (hw_params, &alsa_period_size, 0) ;
	snd_pcm_hw_params_get_buffer_size (hw_params, &buffer_size) ;
	if (alsa_period_size == buffer_size)
	{	fprintf (stderr, "Can't use period equal to buffer size (%lu == %lu)", alsa_period_size, buffer_size) ;
		goto catch_error ;
		} ;
  snd_pcm_hw_params_get_rate (hw_params, &val, &dir);
  fprintf (stderr, "Actual rate (%u)  Direction = %d\n", val, dir);
  snd_pcm_hw_params_get_channels (hw_params, &val);
  fprintf (stderr, "Actual channels (%u)\n", val);
  snd_pcm_hw_params_get_periods (hw_params, &val, &dir);
  fprintf (stderr, "Actual period_size (%u)  Direction = %d\n", val, dir);
  snd_pcm_hw_params_get_buffer_size (hw_params, &lval);
  fprintf (stderr, "Actual buffer_size (%lu)\n", lval);

	snd_pcm_hw_params_free (hw_params) ;

	if ((err = snd_pcm_sw_params_malloc (&sw_params)) != 0)
	{	fprintf (stderr, "%s: snd_pcm_sw_params_malloc: %s", __func__, snd_strerror (err)) ;
		goto catch_error ;
		} ;

	if ((err = snd_pcm_sw_params_current (alsa_dev, sw_params)) != 0)
	{	fprintf (stderr, "%s: snd_pcm_sw_params_current: %s", __func__, snd_strerror (err)) ;
		goto catch_error ;
		} ;

	/* note: set start threshold to delay start until the ring buffer is full */
	snd_pcm_sw_params_current (alsa_dev, sw_params) ;
	if ((err = snd_pcm_sw_params_get_xfer_align (sw_params, &xfer_align)) < 0)
	{	fprintf (stderr, "cannot get xfer align (%s)\n", snd_strerror (err)) ;
		goto catch_error ;
		} ;

	/* round up to closest transfer boundary */
	start_threshold = (buffer_size / xfer_align) * xfer_align ;
	if (start_threshold < 1)
		start_threshold = 1 ;
	if ((err = snd_pcm_sw_params_set_start_threshold (alsa_dev, sw_params, start_threshold)) < 0)
	{	fprintf (stderr, "cannot set start threshold (%s)\n", snd_strerror (err)) ;
		goto catch_error ;
		} ;

	if ((err = snd_pcm_sw_params (alsa_dev, sw_params)) != 0)
	{	fprintf (stderr, "%s: snd_pcm_sw_params: %s", __func__, snd_strerror (err)) ;
		goto catch_error ;
		} ;

	snd_pcm_sw_params_free (sw_params) ;

	snd_pcm_reset (alsa_dev) ;

catch_error :

	if (err < 0 && alsa_dev != NULL)
	{	snd_pcm_close (alsa_dev) ;
		return NULL ;
		} ;

	return alsa_dev ;
} /* alsa_open */

/* Threaded version of alsa write function, args in passed structure */
void *
alsa_write (void *call_parms)
{	
  int epipe_count = 0 ;
	snd_pcm_status_t *status ;
	int total = 0 ;
	int retval = 0 ;

  pthread_mutex_lock (&mtx_play);  // prevent main from calling while processing
  /* extract calling parameters from passed structure */
  slice *sound_slice = (slice *) call_parms;
  snd_pcm_t *alsa_dev = sound_slice->alsa_dev;
  double *data = sound_slice->buffer;
  int frames = sound_slice->frames;
  int channels = sound_slice->channels;

	if (epipe_count > 0)
		epipe_count -- ;

	while (total < frames)
  {	
    retval = snd_pcm_writei (alsa_dev, data + total * channels, frames - total) ;

		if (retval >= 0)
		{	total += retval ;
			if (total == frames)
      {
        pthread_mutex_unlock (&mtx_play);  // allow main to call again
        alsa_write_retval = total;
				return &alsa_write_retval ;
      }
      printf ("alsa_write: partial write %d\n", retval) ;
			continue ;
    } ;

		switch (retval)
		{	case -EAGAIN :
					puts ("alsa_write: EAGAIN  - buffer full") ;
					continue ;
					break ;

			case -EPIPE :
					if (epipe_count > 0)
					{	printf ("alsa_write: EPIPE xrun %d\n", epipe_count) ;
						if (epipe_count > 140)
            {
              pthread_mutex_unlock (&mtx_play);  // allow main to call again
              return &alsa_write_retval ;
            }
          } ;
					epipe_count += 100 ;

					if (0)
					{	snd_pcm_status_alloca (&status) ;
						if ((retval = snd_pcm_status (alsa_dev, status)) < 0)
							fprintf (stderr, "alsa_out: xrun. can't determine length\n") ;
						else if (snd_pcm_status_get_state (status) == SND_PCM_STATE_XRUN)
						{	struct timeval now, diff, tstamp ;

							gettimeofday (&now, 0) ;
							snd_pcm_status_get_trigger_tstamp (status, &tstamp) ;
							timersub (&now, &tstamp, &diff) ;

							fprintf (stderr, "alsa_write xrun: of at least %.3f msecs. resetting stream\n",
									diff.tv_sec * 1000 + diff.tv_usec / 1000.0) ;
            }
						else
							fprintf (stderr, "alsa_write: xrun. can't determine length\n") ;
          } ;

					snd_pcm_prepare (alsa_dev) ;
					break ;

			case -EBADFD :
					fprintf (stderr, "alsa_write: Bad PCM state.n") ;
          pthread_mutex_unlock (&mtx_play);  // allow main to call again
					alsa_write_retval = 0;
          return &alsa_write_retval ;
					break ;

			case -ESTRPIPE :
					fprintf (stderr, "alsa_write: Suspend event.n") ;
          pthread_mutex_unlock (&mtx_play);  // allow main to call again
					alsa_write_retval = 0;
          return &alsa_write_retval ;
					break ;

			case -EIO :
					puts ("alsa_write: EIO") ;
          pthread_mutex_unlock (&mtx_play);  // allow main to call again
					alsa_write_retval = 0;
          return &alsa_write_retval ;

			default :
					fprintf (stderr, "alsa_write: retval = %d\n", retval) ;
          pthread_mutex_unlock (&mtx_play);  // allow main to call again
					alsa_write_retval = 0;
          return &alsa_write_retval ;
					break ;
    } ; /* switch */
  } ; /* while */
  pthread_mutex_unlock (&mtx_play);  // allow main to call again
	alsa_write_retval = total ;
  return &alsa_write_retval ;
} /* alsa_write */

static int
alsa_write_double (snd_pcm_t *alsa_dev, double *data, int frames, int channels)
{	static	int epipe_count = 0 ;

	snd_pcm_status_t *status ;
	int total = 0 ;
	int retval ;

	if (epipe_count > 0)
		epipe_count -- ;

	while (total < frames)
  {	
    retval = snd_pcm_writei (alsa_dev, data + total * channels, frames - total) ;

		if (retval >= 0)
		{	total += retval ;
			if (total == frames)
				return total ;
			continue ;
    } ;

		switch (retval)
		{	case -EAGAIN :
					puts ("alsa_write_double: EAGAIN") ;
					continue ;
					break ;

			case -EPIPE :
					if (epipe_count > 0)
					{	printf ("alsa_write_double: EPIPE %d\n", epipe_count) ;
						if (epipe_count > 140)
							return retval ;
						} ;
					epipe_count += 100 ;

					if (0)
					{	snd_pcm_status_alloca (&status) ;
						if ((retval = snd_pcm_status (alsa_dev, status)) < 0)
							fprintf (stderr, "alsa_out: xrun. can't determine length\n") ;
						else if (snd_pcm_status_get_state (status) == SND_PCM_STATE_XRUN)
						{	struct timeval now, diff, tstamp ;

							gettimeofday (&now, 0) ;
							snd_pcm_status_get_trigger_tstamp (status, &tstamp) ;
							timersub (&now, &tstamp, &diff) ;

							fprintf (stderr, "alsa_write_double xrun: of at least %.3f msecs. resetting stream\n",
									diff.tv_sec * 1000 + diff.tv_usec / 1000.0) ;
							}
						else
							fprintf (stderr, "alsa_write_double: xrun. can't determine length\n") ;
						} ;

					snd_pcm_prepare (alsa_dev) ;
					break ;

			case -EBADFD :
					fprintf (stderr, "alsa_write_double: Bad PCM state.n") ;
					return 0 ;
					break ;

			case -ESTRPIPE :
					fprintf (stderr, "alsa_write_double: Suspend event.n") ;
					return 0 ;
					break ;

			case -EIO :
					puts ("alsa_write_double: EIO") ;
					return 0 ;

			default :
					fprintf (stderr, "alsa_write_double: retval = %d\n", retval) ;
					return 0 ;
					break ;
    } ; /* switch */
  } ; /* while */
	return total ;
} /* alsa_write_double */

#ifdef NOTDEFINED  /* code not used */
static int
alsa_write_int32 (snd_pcm_t *alsa_dev, int *data, int frames, int channels)
{	static	int epipe_count = 0 ;

	snd_pcm_status_t *status ;
	int total = 0 ;
	int retval ;

	if (epipe_count > 0)
		epipe_count -- ;

	while (total < frames)
  {	
    retval = snd_pcm_writei (alsa_dev, data + (total * channels), (frames - total)) ;

		if (retval >= 0)
		{	total += retval ;
			if (total == frames)
				return total ;
			continue ;
    } ;

		switch (retval)
		{	case -EAGAIN :
					puts ("alsa_write_int32: EAGAIN") ;
					continue ;
					break ;

			case -EPIPE :
					if (epipe_count > 0)
					{	printf ("alsa_write_int32: EPIPE %d\n", epipe_count) ;
						if (epipe_count > 140)
							return retval ;
						} ;
					epipe_count += 100 ;

					if (0)
					{	snd_pcm_status_alloca (&status) ;
						if ((retval = snd_pcm_status (alsa_dev, status)) < 0)
							fprintf (stderr, "alsa_out: xrun. can't determine length\n") ;
						else if (snd_pcm_status_get_state (status) == SND_PCM_STATE_XRUN)
						{	struct timeval now, diff, tstamp ;

							gettimeofday (&now, 0) ;
							snd_pcm_status_get_trigger_tstamp (status, &tstamp) ;
							timersub (&now, &tstamp, &diff) ;

							fprintf (stderr, "alsa_write_int32 xrun: of at least %.3f msecs. resetting stream\n",
									diff.tv_sec * 1000 + diff.tv_usec / 1000.0) ;
							}
						else
							fprintf (stderr, "alsa_write_int32: xrun. can't determine length\n") ;
						} ;

					snd_pcm_prepare (alsa_dev) ;
					break ;

			case -EBADFD :
					fprintf (stderr, "alsa_write_int32: Bad PCM state.n") ;
					return 0 ;
					break ;

			case -ESTRPIPE :
					fprintf (stderr, "alsa_write_int32: Suspend event.n") ;
					return 0 ;
					break ;

			case -EIO :
					puts ("alsa_write_int32: EIO") ;
					return 0 ;

			default :
					fprintf (stderr, "alsa_write_int32: retval = %d\n", retval) ;
					return 0 ;
					break ;
    } ; /* switch */
  } ; /* while */
	return total ;
} /* alsa_write_int32 */

#endif /* NOTDEFINED */

long
check_samplerate (char *inname)
{	
  SNDFILE *infile ;
	SF_INFO sfinfo ;
	double src_ratio = -1.0;
	int new_sample_rate = out_rate;

	if (! (infile = sf_open (inname, SFM_READ, &sfinfo)))
	  error ("Error : Not able to open input file '%s'\n", inname) ;

	printf ("Input File    : %s\n", inname) ;
	printf ("Sample Rate   : %d\n", sfinfo.samplerate) ;
	printf ("Input Frames  : %ld\n\n", (long) sfinfo.frames) ;

	src_ratio = (1.0 * new_sample_rate) / sfinfo.samplerate ;
  if (src_ratio != 1.0)  // change in rate
  {
    SNDFILE *outfile ;
    sf_count_t count ;
    double gain = 1.0 ;
      /* Set default converter. */
    int converter = SRC_SINC_BEST_QUALITY ;

    printf ("SRC Ratio     : %f\n", src_ratio) ;
    printf ("Converter     : %s\n\n", src_get_name (converter)) ;
    /* Create the name for the new output file by appending the new rate to the input file */
    char * ppos = strchr (inname, '.');  // last period
    char * spos = strchr (inname, '/');  // last slash
    char qual [256];
    if (ppos != NULL  && ((spos != NULL && (ppos - spos) > 0) || (spos == NULL)))  // last period after last slash
    {
      sprintf (qual, "%s", ppos);  // save file qualifier
      *ppos = '\0'; // remove it from inname
    }
    else
      qual[0] = '\0';
    char strrate[8];
    sprintf (strrate, "_%d", new_sample_rate);
    strcat (inname, strrate);
    strcat (inname, qual);
    /* Delete the output file length to zero if already exists. */
    remove (inname) ;
    sfinfo.samplerate = new_sample_rate ;
    if ((outfile = sf_open (inname, SFM_WRITE, &sfinfo)) == NULL)
     	error ("Error : Not able to open output file '%s'\n", inname) ;
    sf_command (outfile, SFC_SET_CLIPPING, NULL, SF_TRUE) ;
    do
      count = sample_rate_convert (infile, outfile, converter, src_ratio, sfinfo.channels, &gain) ;
    while (count < 0) ;
    printf ("Output file   : %s\n", inname) ;
    printf ("Sample Rate   : %d\n", sfinfo.samplerate) ;
    printf ("Output Frames : %ld\n\n", (long) count) ;
    sf_close (infile) ;
    sf_close (outfile) ;
    return (long) count ;
  }
  else  // no change in rate
  {
    sf_close (infile) ;
    return 0L ;
  }
} /* check_samplerate */

/*==============================================================================
*/

//#define	BUFFER_LEN		4096	/*-(1<<16)- from example program */
static sf_count_t
sample_rate_convert (SNDFILE *infile, SNDFILE *outfile, int converter, double src_ratio, int channels, double * gain)
{	
  static float input [2*BUFFER_LEN] ;
	static float output [2*BUFFER_LEN] ;

	SRC_STATE	*src_state ;
	SRC_DATA	src_data ;
	int			error ;
	double		max = 0.0 ;
	sf_count_t	output_count = 0 ;

	sf_seek (infile, 0, SEEK_SET) ;
	sf_seek (outfile, 0, SEEK_SET) ;

	/* Initialize the sample rate converter. */
	if ((src_state = src_new (converter, channels, &error)) == NULL)
	{	printf ("\n\nError : src_new() failed : %s.\n\n", src_strerror (error)) ;
		exit (1) ;
  } ;

	src_data.end_of_input = 0 ; /* Set this later. */

	/* Start with zero to force load in while loop. */
	src_data.input_frames = 0 ;
	src_data.data_in = input ;

	src_data.src_ratio = src_ratio ;

	src_data.data_out = output ;
	src_data.output_frames = (2*BUFFER_LEN) /channels ;

	while (1)
	{
		/* If the input buffer is empty, refill it. */
		if (src_data.input_frames == 0)
		{	src_data.input_frames = sf_readf_float (infile, input, (2*BUFFER_LEN) / channels) ;
			src_data.data_in = input ;

			/* The last read will not be a full buffer, so snd_of_input. */
			if (src_data.input_frames < (2*BUFFER_LEN) / channels)
				src_data.end_of_input = SF_TRUE ;
    } ;

		if ((error = src_process (src_state, &src_data)))
		{	printf ("\nError : %s\n", src_strerror (error)) ;
			exit (1) ;
    } ;

		/* Terminate if done. */
		if (src_data.end_of_input && src_data.output_frames_gen == 0)
			break ;

		max = apply_gain (src_data.data_out, src_data.output_frames_gen, channels, max, *gain) ;

		/* Write output. */
		sf_writef_float (outfile, output, src_data.output_frames_gen) ;
		output_count += src_data.output_frames_gen ;

		src_data.data_in += src_data.input_frames_used * channels ;
		src_data.input_frames -= src_data.input_frames_used ;
  } ;

	src_state = src_delete (src_state) ;

	if (max > 1.0)
	{	
    *gain = 1.0 / max ;
		printf ("\nOutput has clipped. Restarting conversion to prevent clipping.\n\n") ;
		output_count = 0 ;
		sf_command (outfile, SFC_FILE_TRUNCATE, &output_count, sizeof (output_count)) ;
		return -1 ;
  } ;

	return output_count ;
} /* sample_rate_convert */

static double
apply_gain (float * data, long frames, int channels, double max, double gain)
{
	long k ;

	for (k = 0 ; k < frames * channels ; k++)
	{	
    data [k] *= gain ;
		if (fabs (data [k]) > max)
			max = fabs (data [k]) ;
  } ;
	return max ;
} /* apply_gain */

