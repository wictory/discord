// discord - binaural and chronaural beat generator
// (c) 2007-2008 Stan Lysiak <stanlk@users.sourceforge.net>.  
// All Rights Reserved.
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
// The following GPL licensed programs were utilized for discord.
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

int opt_a;                      // audio card and device set in options
char *opt_a_plughw = NULL;      // audio card and device to use
int opt_b;                      // bit accuracy of output
int bit_accuracy = SF_FORMAT_PCM_16;  // bit accuracy of file output defaults to 16
int opt_c;                      // Compensate for human hearing low and high freq dropoff
int opt_c_points = 0;           // Number of -c option points provided (max 32)
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
int opt_k = 0;                  // keep resampled files, default delete them
int opt_m = 0;                  // modify carrier and beat in script file by a random percentage +/-
double opt_m_arg = 0.0;         // percentage in decimal form of modification band for carrier and beat
double modify = 0.0;            // percentage in decimal form of modification band for carrier and beat
int opt_o;                      // output format to write
int outfile_format = SF_FORMAT_FLAC; // default to flac if not specified otherwise, r:raw, f:flac
int opt_q;                      // quiet run, no display of sequence
int opt_r;                      // samples per second requested
int out_rate = 44100;           // samples per second, default to cd standard
int opt_t;                      // use thread to play sound instead of blocking function call
int opt_w;                      // write file instead of sound
char *out_filename;           // write file instead of sound
const char *separators = "='|,;";  // separators for time sequences, mix and match, multiples ok
double *sin_table;
int status_t_retval = 0;  // return integer for status_t thread
int alsa_write_retval = 0;  // return integer for alsa_write thread
int msec_fade_count;      // how many frames to make a millisecond
double msec_fade_adjust;  // how much to adjust so that msec_fade_count * msec_fade_adjust = 1.0

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

/* string of saved options for each possible source
 * in order of priority
 */
saved_option *ARGV_OPTIONS = NULL;
saved_option *SCRIPT_OPTIONS = NULL;
saved_option *CONFIG_OPTIONS = NULL;

/* node to contain a time sequence
   line */
typedef struct time_seq time_seq;
struct time_seq
{
  struct time_seq *prev;
  struct time_seq *next;
  char *sequence;
} ;
/* holds a time sequence list */
time_seq *TS = NULL;

/* node to contain a sound file buffer */
typedef struct snd_buffer snd_buffer;
struct snd_buffer
{
  struct snd_buffer *prev;
  struct snd_buffer *next;
  char *filename;
  short *sound;
  int_64 frames;
  int channels;
  int mono;
  double scale;
} ;
/* list of buffers from sound files */
snd_buffer *Sound_Files = NULL;

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
  int type;                 // 1  Can be 9 for step, 11 for vary
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
  double amp_beat1_adj, amp_beat2_adj, amp_pct1_adj, amp_pct2_adj;   // amp pulse continuous adjustment if desired
  int slide;     // 1 if this sequence slides into the next (only binaurals slide)
    /* to avoid discontinuities at the join between voices, use last offset into sin table of previous voice as
        starting offset for this voice.  Store a pointer to it during setup.
    */
  int *last_off1, *last_off2;   
  int *last_amp_off1, *last_amp_off2;   
  int first_pass;  // is this voice inactive?
  /* used for step and vary */
  binaural *step_next;  // point to linked list of binaural voices for steps and vary
  int_64 tot_frames;  // total frames for this step
  int_64 cur_frames;  // current frames for this step
  int steps;  // number of steps if selected
  double slide_time;  // how many seconds to slide between steps
  double fuzz;  // how much fuzziness around step frequency, per cent as decimal.
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
  // 6 increase sinusoidally to 1.0 and back to 0.0
  // 7 decrease sinusoidally to -1.0 and back to 0.0
  // 8-14 above with 10% carrier drop
  // 15-21 above with 10% carrier rise
  // values the same, then constant
  int inc1, off1;               // for noise tones, offset + increment into sine
  int_64 next_play, sofar;             // Samples till next noise, how many so far
  int_64 play;                    // number of frames to play the noise
  double carrier_adj, amp_adj, split_adj;      // adjust while noise is playing
  double behave_inc1, behave_off1;      // for adjust behavior 6 and 7, offset and inc into sine
  double fade_factor;           // used to adjust volume when doing 1 millisec fade out at end of play.
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
  int_64 size;   // Frames for each sample
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
  int_64 play_when;  // when to play the sound
  int_64 sofar;   // Frames, how many so far
  int_64 play;  //offset into buffer in frames, frames that have been played
  int_64 off1;  //short offset into buffer
  double split_adj; // adjust split while sound is playing
  int mono;  // can be mono sound even with 2 channels.  0:stereo, 1:left mono, 2:right mono
  int not_played;  // has the single play occurred yet?
} ;

/* structure for playing a chronaural beat */
typedef struct chronaural chronaural;
struct chronaural
{
  void *prev;
  void *next;
  int type;                 // 8, or 10 for chronaural step slide, 12 for vary
  double carrier;               // Carrier freq
  double beat;   // Beat frequency of carrier frequency
  double amp;   // Amplitude level 0-100%, stored as decimal. i.e. .06
  double phase;                 // Phase between left and right channel, 0 to 360 degrees.
                                // Beat +ve, left starts at zero, right channel phase shifts.
                                // Beat -ve, right starts at zero, left channel phase shifts.
                                // 0 or 360 means in phase.
  double sin_threshold;   // Value of sin at which to begin the chronaural beat
  int beat_behave;
  /* amplitude behavior of chronaural beat:
     1 sine wave
     2 square wave
     3 dirac delta approximation, 5th power of sin value
     4 extreme dirac delta approximation, 15th power of sin value
  */
  double split_begin, split_end, split_now;      // left fraction for chronaural, .5 means evenly split L and R
  double split_low, split_high; // range for split, .5 means evenly split L and R
  double split_beat;   // Split variation frequency, defaults to beat
  int slide;     // 1 if this sequence slides into the next (binaurals and chronaurals slide)
  int inc1, off1;               // for chronaural tones, offset + increment into sine table for carrier of left channel
  int inc3, off3;               // for chronaural tones, offset + increment into sine table for carrier of right channel
  int off2;               // offset into sine table for beat
  double inc2;            // increment of offset into sine table for beat
  double carr_adj, beat_adj, amp_adj, phase_adj;   // continuous adjustment if desired
  double split_beat_adj, split_adj;   // continuous adjustment if desired
    /* to avoid discontinuities at the join between voices, use last offset into sin table of previous voice as
        starting offset for this voice.  Store a pointer to it during setup.
    */
  int *last_off1, *last_off3, *last_off2;   
  int first_pass;  // is this voice inactive?
  chronaural *step_next;  // point to linked list of chronaural voices for steps or vary
  int_64 tot_frames;  // total frames for this step
  int_64 cur_frames;  // current frames for this step
  int steps;  // number of steps if selected
  double slide_time;  // how many seconds to slide between steps
  double fuzz;  // how much fuzziness around step frequency, per cent as decimal.
  double fade_factor;  // current fade out multiplier for unshifted channel, no fade in as always start at zero.
  double fade_factor2;  // current fade out multiplier for shifted channel, no fade in as always start at zero.
  double fade_sinval;  // sinval where fade in ended and at which to start fade out (sine is symmetric) for unshifted channel
  double fade_sinval2;  // sinval where fade in ended and at which to start fade out (sine is symmetric) for shifted channel
} ;

/* structure for playing a pulse, a fixed time chronaural beat 
 * The pulse is always a square wave, on fully or off */
typedef struct pulse pulse;
struct pulse
{
  void *prev;
  void *next;
  int type;                 // 13, or 14 for pulse step slide, 15 for vary
  double carrier;               // Carrier freq
  double beat;   // Pulse beat frequency of carrier frequency
  double amp;   // Amplitude level 0-100%, stored as decimal. i.e. .06
  double phase;                 // Phase between left and right channel, 0 to 360 degrees.
                                // Beat +ve, left starts at zero, right channel phase shifts.
                                // Beat -ve, right starts at zero, left channel phase shifts.
                                // 0 or 360 means in phase.  Yes, it is redundant, -177 == +183, for ease of specification
  double time;   // Duration of the pulse in seconds
  int frames_left; // Number of frames for the current pulse in the left channel, depends on pulse time
  int frames_right; // Number of frames for the current pulse in the right channel, depends on pulse time
  double split_begin, split_end, split_now;      // left fraction for pulse, .5 means evenly split L and R
  double split_low, split_high; // range for split, .5 means evenly split L and R
  double split_beat;   // Split variation frequency, defaults to beat
  double split_dist;   // Split distance between split_begin and split_end.  Used only when there is a split_beat.
  int slide;     // nonzero if this sequence slides into the next (binaurals, chronaurals, and phases slide)
  int inc1, off1;               // for pulse tones, offset + increment into sine table for carrier of left channel
  int inc3, off3;               // for pulse tones, offset + increment into sine table for carrier of right channel
  int off2;               // offset into sine table for beat
  double inc2;            // increment of offset into sine table for beat
  double carr_adj, beat_adj, time_adj, amp_adj, phase_adj;   // continuous adjustment if desired
  double split_beat_adj, split_adj;   // continuous adjustment if desired for pan or pan beat
    /* to avoid discontinuities at the join between voices, use last offset into sin table of previous voice as
        starting offset for this voice.  Store a pointer to it during setup.  */
  int *last_off1, *last_off3, *last_off2;   
  int first_pass;  // is this voice inactive?
  pulse *step_next;  // point to linked list of pulse voices for steps or vary
  int_64 tot_frames;  // total frames for this step
  int_64 cur_frames;  // current frames for this step
  int steps;  // number of steps if selected
  double slide_time;  // how many seconds to slide between steps
  double fuzz;  // how much fuzziness around step frequency, per cent as decimal.
  double fade_factor_left;  // current fade out multiplier for left channel, no fade in as always start at zero.
  double fade_factor_right;  // current fade out multiplier for right channel, no fade in as always start at zero.
} ;

/* structure to set a phase beat */
typedef struct phase phase;
struct phase
{
  void *prev;
  void *next;
  int type;                 // 16  Can be 17 for step, 18 for vary
  double carrier;               // Carrier freq
  double beat;                  // Phase shift frequency, equivalent to beat freq
  double amp;                   // Amplitude level 0-100%, stored as decimal. i.e. .06
  double phase;                 // Phase between left and right channel, 0 to 360 degrees.
                                // Beat +ve, left starts at zero, right channel phase shifts.
                                // Beat -ve, right starts at zero, left channel phase shifts.
                                // 0 or 360 means in phase.
  double amp_beat1, amp_beat2;  // Amplitude beat for each channel, frequency of variation
  double amp_pct1, amp_pct2;    // Amplitude adjustment for each channel, per cent band to vary +/- within
  int inc1, off1;               // for phase tones, offset + increment into sin table for each channel
  int shift;                    // cumulative shift for phase adjustment
  int direction;                // direction that phase adjust is moving, +ve towards max phase, -ve towards in phase
  int amp_inc1, amp_off1;       // sin table ofset and increment for left amp
  int amp_inc2, amp_off2;       // sin table ofset and increment for right amp
  double carr_adj, beat_adj, amp_adj, phase_adj;   // continuous adjustment if desired
  double amp_beat1_adj, amp_beat2_adj, amp_pct1_adj, amp_pct2_adj;   // amp pulse continuous adjustment if desired
  int slide;     // 1 if this sequence slides into the next (only phases slide)
    /* to avoid discontinuities at the join between voices, use last offset into sin table of previous voice as
        starting offset for this voice.  Store a pointer to it during setup.
    */
  int *last_off1, *last_shift, *last_direction;
  int *last_amp_off1, *last_amp_off2;   
  int first_pass;  // is this voice inactive?
  /* used for step and vary */
  phase *step_next;  // point to linked list of phase voices for steps and vary
  int_64 tot_frames;  // total frames for this step
  int_64 cur_frames;  // current frames for this step
  int steps;  // number of steps if selected
  double slide_time;  // how many seconds to slide between steps
  double fuzz;  // how much fuzziness around step frequency, per cent as decimal.
} ;

/* structure to set a fm beat */
typedef struct fm fm;
struct fm
{
  void *prev;
  void *next;
  int type;                 // 19  Can be 20 for step, 21 for vary
  double carrier;               // Carrier freq
  double beat;                  // Frequency that carrier shifts between carrier and carrier plus band.
  double amp;                   // Amplitude level 0-100%, stored as decimal. i.e. .06
  double band;                  // Frequency band to shift within, Hz relative to carrier 
                                // Band must be +ve and will shift up from carrier by this amount.
  char channel;                 // L, R, or B standing for left channel, right channel, or both.
  double phase;                 // Phase between left and right channel, -360 to +360 degrees.
                                // Phase +ve, right channel phase shifted that amount relative to left.
                                // Phase -ve, left channel phase shifted that amount relative to right.
                                // 0 or 360 means in phase.  Redundancy for ease of specification.
                                // only meaningful when channel is B
  double amp_beat1, amp_beat2;  // Amplitude beat for each channel, frequency of variation
  double amp_pct1, amp_pct2;    // Amplitude adjustment for each channel, per cent band to vary +/- within
  int inc1, off1;               // for fm tones, offset + increment into sin table for each channel
  double shift;                 // cumulative shift for freq adjustment to the carrier, moves between 0 and band
  int direction;                // direction that freq adjust is moving, +ve towards band, -ve towards carrier
  int amp_inc1, amp_off1;       // sin table ofset and increment for left amp
  int amp_inc2, amp_off2;       // sin table ofset and increment for right amp
  double carr_adj, beat_adj, amp_adj, phase_adj;   // continuous adjustment if desired    
  double band_adj;              // continuous adjustment if desired    
  double amp_beat1_adj, amp_beat2_adj, amp_pct1_adj, amp_pct2_adj;   // amp pulse continuous adjustment if desired
  int slide;     // 1, 2, or 3 if this sequence slides into the next (only fms slide)
    /* to avoid discontinuities at the join between voices, use last offset into sin table of previous voice as
        starting offset for this voice.  Store a pointer to it during setup.
    */
  int *last_off1;
  double *last_shift;
  int *last_direction;
  int *last_amp_off1, *last_amp_off2;   
  int first_pass;  // is this voice inactive?
  /* used for step and vary */
  fm *step_next;  // point to linked list of fm voices for steps and vary
  int_64 tot_frames;  // total frames for this step
  int_64 cur_frames;  // current frames for this step
  int steps;  // number of steps if selected
  double slide_time;  // how many seconds to slide between steps
  double fuzz;  // how much fuzziness around step frequency, per cent as decimal.
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
int parse_discordrc ();
int set_options (saved_option *SO);
int setup_play_seq ();
int read_script_file (FILE *infile, char **config_options);
int read_config_file (FILE *infile, char **config_options);
int append_options (saved_option **SO, char *config_options);
int setup_opt_c (char *spec);
void setup_binaural (char *token, void **work);
void setup_bell (char *token, void **work);
int setup_noise (char *token, void **work);
void setup_stoch (char *token, void **work);
void setup_sample (char *token, void **work);
void setup_repeat (char *token, void **work);
void setup_once (char *token, void **work);
void setup_chronaural (char *token, void **work);
void setup_pulse (char *token, void **work);
void setup_phase (char *token, void **work);
void setup_fm (char *token, void **work);
void finish_beat_voice_setup ();
snd_buffer * process_sound_file (char *filename);
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
void alsa_validate_device_and_rate ();
static snd_pcm_t *alsa_open (snd_pcm_t *alsa_dev, int channels, unsigned samplerate, int realtime);
static int alsa_write_double (snd_pcm_t *alsa_dev, double *data, int frames, int channels) ;
void alsa_write (void *call_parms); // version for threading
void file_write (void *call_parms); // version for threading
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
  error ("discord - Create and mix binaural, chronaural and phase beats, version " VERSION NL
         "Copyright (c) 2007-2008 Stan Lysiak, all rights reserved," NL
         "released under the GNU GPL v2.  See file COPYING." NL NL
         "Usage: discord [options] sequence-file" NL NL
         "Control-C to quit while running" NL NL
         "For full usage help, type 'discord -h'.  For latest version see" NL
         "http://sourceforge.net/projects/discord/"NL);
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
  /* set the command line options before all others so they will 
   * be in effect while the rest of the options are parsed and set.
   * In particular, this prevents printing of compensation arrays
   * when quiet is set.
   */
  set_options (ARGV_OPTIONS);
  parse_argv_configs (argc, argv); // parse script/sequence files
  parse_discordrc (); // parse discord configuration file
  set_options (CONFIG_OPTIONS);  // set the configuration options, lowest priority
  set_options (SCRIPT_OPTIONS);  // set the script file options, next priority
  set_options (ARGV_OPTIONS);  // reset the command line options, highest priority
  /* validate device and hardware rate 
   * before sin table size, frame rate 
   * and any resample are set */
  alsa_validate_device_and_rate ();
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
  const char *ostr = "a:b:c:de:f:hkm:o:qr:tw:";
  int c;
  int option_index = 0;
  saved_option *soh = NULL, *sow = NULL;
  static struct option long_options[] =
    {
      {"audio_device", 1, 0, 'a'},
      {"bit_accuracy", 1, 0, 'b'},
      {"compensate", 1, 0, 'c'},
      {"display_only", 0, 0, 'd'},
      {"every", 1, 0, 'e'},
      {"fast", 1, 0, 'f'},
      {"help", 0, 0, 'h'},
      {"keep", 0, 0, 'k'},
      {"modify", 1, 0, 'm'},
      {"out_format", 1, 0, 'o'},
      {"quiet", 0, 0, 'q'},
      {"rate", 1, 0, 'r'},
      {"thread", 0, 0, 't'},
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

      case 'a':
      case 'b':
      case 'c':
      case 'd':
      case 'e':
      case 'f':
      case 'h':
      case 'k':
      case 'm':
      case 'o':
      case 'q':
      case 'r':
      case 't':
      case 'w':
        soh = (saved_option *) Alloc ((sizeof (saved_option)) * 1);
        soh->next = NULL;
        if (ARGV_OPTIONS == NULL)         // option list doesn't exist
        {
          soh->prev = NULL;
          ARGV_OPTIONS = soh;
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

/* parses the sequence files for
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
      if (!infile)
        error ("Unable to open script file %s", filename);
      read_script_file (infile, &config_options);
      append_options (&SCRIPT_OPTIONS, config_options);
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
append_options (saved_option **SO, char *config_options)
{
  const char *ostr = "a:b:c:de:f:hkm:o:qr:tw:";
  char *found;
  char *token, *subtoken;
  char *str1, *str2;
  char *saveptr1, *saveptr2;
  int tlen;
  saved_option *soh = NULL, *sow = NULL;
  static struct option long_options[] =
    {
      {"audio_device", 1, 0, 'a'},
      {"bit_accuracy", 1, 0, 'b'},
      {"compensate", 1, 0, 'c'},
      {"display_only", 0, 0, 'd'},
      {"every", 1, 0, 'e'},
      {"fast", 1, 0, 'f'},
      {"help", 0, 0, 'h'},
      {"keep", 0, 0, 'h'},
      {"modify", 1, 0, 'm'},
      {"out_format", 1, 0, 'o'},
      {"quiet", 0, 0, 'q'},
      {"rate", 1, 0, 'r'},
      {"thread", 0, 0, 't'},
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
    if (*SO == NULL)             // option list doesn't exist, no command line options
    {
      soh->prev = NULL;
      *SO = soh;
    }
    else
    {
      if (sow == NULL)  // first time through, there are command line options
      {
        sow = *SO;  // start at root of linked list of options
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
          sow->option = long_options[long_idx].val;    // assign short option
          if (long_options[long_idx].has_arg == 1)      // has argument
          {
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
   Read a script file, discarding blank
   lines and comments.  Rets: 0 on success.
   Everything from the file is put into a character
   string for options, or a linked list for play sequences. */

int
read_script_file (FILE * infile, char **config_options)
{
  char *curlin, *cmnt, *token;
  char savelin[16384], worklin[16384], rawline[16384];
  size_t len, destlen;
  int line_count = 0;
  time_seq *tsh = NULL, *tsw = NULL;

  memset (savelin, 0x00, 16384);
  memset (worklin, 0x00, 16384);
  fgets (worklin, sizeof (worklin), infile);
  strncpy (rawline, worklin, 16384); // strtok is destructive, save raw copy of line
  curlin = rawline;
  while (*curlin != '\0')
  {
    line_count++;
    token = strtok (worklin, " \t\n");    // get first token separated by spaces, tabs, or newline
    if (token)                  // not an empty line
    {
      cmnt = strchr (curlin, '#');
      if (cmnt && cmnt[1] == '#')
      {
        if (!opt_q)  // quiet
        {
          fprintf (stderr, "Configuration comment  %s\n", curlin);
          fflush (stderr);
        }
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
          memset (savelin, 0x00, 16384);         // reset saved line
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
          memset (savelin, 0x00, 16384);         // reset saved line
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
        else if (destlen + len + 1 < 16384)
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
      {
        if (!opt_q)  // quiet
          fprintf (stderr, "Skipped line with token %s at start of line\n", token);
      }
    }
    memset (worklin, 0x00, 16384);
    fgets (worklin, sizeof (worklin), infile);
    strncpy (rawline, worklin, 16384); // strtok is destructive, save raw copy of line
    curlin = rawline;
  }
  if (*curlin == '\0')
  {
    if (feof (infile))
    {                           
      // save last time sequence
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

/* parses the discord configuration file
   options.  Places them in linked list.
*/
int
parse_discordrc ()
{
  char *homedir;
  // points to a string containing all the configuration file options
  char *config_options = NULL;
  struct stat stat_buffer;
  
  homedir = getenv("HOME");
  if ((homedir != NULL) && strlen(homedir))
  {
    char config_file [512] = {'\0'};

    strncpy (config_file, homedir, sizeof(config_file) - 1);
    strcat (config_file, "/.discordrc");
    int retval = stat(config_file, &stat_buffer);
    if (retval != -1)
    {
      FILE *infile;

      infile = fopen (config_file, "r");
      if (!infile)
        error ("Unable to open configuration file %s", config_file);
      read_config_file (infile, &config_options);
      append_options (&CONFIG_OPTIONS, config_options);
      fclose (infile);
      return 1;
    }
    return 0;
  }
  return 0;
}

/*
   Read a configuration file, discarding blank
   lines and comments.  Rets: 0 on success.
   Everything from the file is put into a character
   string for options.
*/

int
read_config_file (FILE * infile, char **config_options)
{
  char *curlin, *cmnt, *token;
  char savelin[16384], worklin[16384], rawline[16384];
  size_t len, destlen;
  int line_count = 0;

  memset (savelin, 0x00, 16384);
  memset (worklin, 0x00, 16384);
  fgets (worklin, sizeof (worklin), infile);
  strncpy (rawline, worklin, 16384); // strtok is destructive, save raw copy of line
  curlin = rawline;
  while (*curlin != '\0')
  {
    line_count++;
    token = strtok (worklin, " \t\n");    // get first token separated by spaces, tabs, or newline
    if (token)                  // not an empty line
    {
      cmnt = strchr (curlin, '#');
      if (cmnt && cmnt[1] == '#')
      {
        if (!opt_q)  // quiet
        {
          fprintf (stderr, "Configuration comment  %s\n", curlin);
          fflush (stderr);
        }
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
      else if (token[0] == '#') // line is a comment
        ;  // do nothing
      else
      {
        if (!opt_q)  // quiet
          fprintf (stderr, "Skipped line %d in script file with invalid %s at start of line\n", 
                          line_count, token);
      }
    }
    memset (worklin, 0x00, 16384);
    fgets (worklin, sizeof (worklin), infile);
    strncpy (rawline, worklin, 16384); // strtok is destructive, save raw copy of line
    curlin = rawline;
  }
  if (*curlin == '\0')
  {
    if (feof (infile))
    {                           
      if (savelin[0] == '-')          // only options in the file, config file
      {
        *config_options = StrDup (savelin);    // save them for further processing
        return 0;
      }
    }
    error ("Read error on sequence file");
  }
  return 0;
}

/*  Process the linked list of options
    pointed to by SO.  Do it in reverse
    so that later options are overridden
    by earlier options. */
int
set_options (saved_option *SO)
{
  char *endptr;
  char *compvals=NULL;
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
      case 'a':  // audio card and device to use for playback
        opt_a = 1;
        if (sow->option_string != NULL)
          opt_a_plughw = StrDup(sow->option_string);
        else
        {
          if (!opt_q)  // quiet
            fprintf (stderr, "No plughw set for --audip_device/-a.  Will use alsa default device.\n");
        }
        break;
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
        {
          if (!opt_q)  // quiet
            fprintf (stderr, "Unrecognized format for --bit_accuracy/-b %s.  Setting to 16 bit.\n", sow->option_string);
          bit_accuracy = SF_FORMAT_PCM_16;
        }
        break;
      case 'c':  // compensate for human hearing, edge freqs need to be louder
        opt_c = 1;
        if (compvals == NULL) 
        {
          size_t compbytes = strlen(sow->option_string);
          compvals = (char *) Alloc(compbytes+2);
          strcpy (compvals, sow->option_string);
          strcat (compvals, "'");  // ensure following separator
        }
        else
        {
          size_t needbytes = strlen(compvals) + strlen(sow->option_string) + 2;
          void *newmem = realloc(compvals, needbytes);
          if (newmem == NULL)
            error ("Unable to extend the compensate options string");
          else
            compvals = (char *) newmem;
          strcat (compvals, sow->option_string);
          strcat (compvals, "'");  // ensure following separator
        }
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
            if (!opt_q)  // quiet
              fprintf (stderr, "Seconds for --every/-e cannot be 0.  Setting to 5.\n");
            every = 5;
          }
          else                  // there was an error
            error ("--every/-e expects integer seconds, %s", sow->option_string);
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
            if (!opt_q)  // quiet
              fprintf (stderr, "Multiplier for --fast/-f cannot be 0.  Setting to 1.\n");
            fast_mult = 1;
          }
          else                  // there was an error
            error ("--fast/-f expects numeric multiplier, %s", sow->option_string);
        }
        else
          fast_mult = (int) fabs (opt_f_arg);
        break;
      case 'h':  // help
        help ();
        break;
      case 'k':                // retain resampled files
        opt_k = 1;
        break;
      case 'm':  // modify the script file carrier and beat frequencies by random amount of percentage provided
        opt_m = 1;
        errno = 0;
        opt_m_arg = strtod (sow->option_string, &endptr);
        if (errno == 0)       // no error
        {
          if (fabs (opt_m_arg) >= 200.)
            error ("Can't modify the carrier or beat to be negative, --modify/-m must be less than 200.");
          if (opt_m_arg < 0.0 && !opt_q)
            fprintf (stderr, "Percentage for --modify/-m cannot be less than 0.  Converting to positive.\n");
          opt_m_arg = AMP_AD (fabs (opt_m_arg));  // convert to positive decimal
          modify = opt_m_arg;  // save in variable
        }
        else                  // there was an error
          error ("--modify/-m expects positive numeric percentage %s", sow->option_string);
        break;
      case 'o':  // output file format
        opt_o = 1;
        if (sow->option_string != NULL)
        {
          if (sow->option_string[0] == 'f' || sow->option_string[0] == 'F')
            outfile_format = SF_FORMAT_FLAC;
          else if (sow->option_string[0] == 'r' || sow->option_string[0] == 'R')
            outfile_format = SF_FORMAT_RAW;
          else if (sow->option_string[0] == 'w' || sow->option_string[0] == 'W')
            outfile_format = SF_FORMAT_WAV;
          else  // default to flac
          {
            if (!opt_q)  // quiet
              fprintf (stderr, "Unrecognized format for --output/-o %c.  Setting to flac.\n", sow->option_string[0]);
            outfile_format = SF_FORMAT_FLAC;
          }
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
          error ("Expecting an integer after --rate/-r %s", sow->option_string);
        break;
      case 't':                // thread sound play
        opt_t = 1;
        break;
      case 'w':  // write to file
        opt_w = 1;
        if (sow->option_string != NULL)
          out_filename = StrDup(sow->option_string);
        else  // default to generic name
          out_filename = "discord_saved_output_file";
        break;
      default:
        error ("Option -%c not known; run 'discord -h' for help", c);
    }
    sow = sow->prev;
  }
  if (compvals != NULL)  // there are new compensation values
  {
    opt_c_points = setup_opt_c (compvals);  // all option lines concatenated into compvals
    if (!opt_q)  // quiet
      fprintf (stderr, "opt_c_points %d\n", opt_c_points);
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
  if (opt_c_points > 0)  // already populated, clear it for higher priority
  {
    int ii;
    for (ii = 0; ii < max_points; ii++)
    {
      compensate[ii].freq = 0.0;
      compensate[ii].adj = 0.0;
    }
  }
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
  free (config);  // reclaim the storage
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
  if (!opt_q)  // quiet
  {
    for (a = 0; a < point_count; a++)
      fprintf (stderr, "compensate freq %g comp %g\n",
                  compensate[a].freq, compensate[a].adj);
  }
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
  adjust = point / 2;  // adjustment step size
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
  printf ("discord - Create binaural and chronaural beats, version " VERSION NL
          "Copyright (c) 2007-2008 Stan Lysiak, all rights reserved," NL
          "released under the GNU GPL v2.  See file COPYING." NL NL
          "http://sourceforge.net/projects/discord/"NL
          "** This program is free software; you can redistribute it and/or modify"NL
          "** it under the terms of the GNU General Public License as published by"NL
          "** the Free Software Foundation; either version 2.1 of the License, or"NL
          "** (at your option) any later version."NL
          "This program is distributed in the hope that it will be useful,"NL
          "but WITHOUT ANY WARRANTY; without even the implied warranty of"NL
          "MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the"NL
          "GNU General Public License for more details."NL
          "You should have received a copy of the GNU General Public License"NL
          "along with this program; if not, write to the Free Software"NL
          "Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA."NL

          "Usage: discord [options] sequence-file" NL NL
          "Control-C to quit while running" NL NL
          "Options:  -h --help         Display this help-text" NL
          "          -a --audio_device Alsa plug device to use.  When not specified, uses default as plughw device"NL
          "          -b --bit_accuracy Number of bits to use to represent each sound: integer or float"NL
          "          -c --compensate   Compensate for human hearing perceptual differences: see docs"NL
          "          -d --display      Display the full interpreted sequence instead of playing it"NL
          "          -e --every        Show a status line every x seconds while playing"NL
          "          -f --fast         Fast.  Run through quickly (real time x 'mult')"NL
          "                              rather than wait for real time to pass"NL
          "          -k --keep         Keep the resampled input sound files"NL
          "          -m --modify       Modify the carrier and beat in script file randomly in percentage band"NL
          "          -o --outfile      Output data to the given file instead of playing"NL
          "          -q --quiet        Don't display running status"NL
          "          -r --rate         Select the output rate (default is 44100 Hz)"NL
          "          -t --thread       Use thread to play sound instead of blocking function call"NL
          "          -w --write        Write an output file instead of playing through sound card"NL);
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

  /* frame rate has been validated, set the millisecond fade global variables */
  msec_fade_count = (int) (round ( out_rate / 1000.));
  msec_fade_adjust = 1.0 / (double) msec_fade_count;

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
      else if (strcasecmp (subtoken, "pulse") == 0)
        setup_pulse (voice, &work);
      else if (strcasecmp (subtoken, "phase") == 0)
        setup_phase (voice, &work);
      else if (strcasecmp (subtoken, "fm") == 0)
        setup_fm (voice, &work);
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
  finish_beat_voice_setup ();  // complete setup of beat voices now that sequences are known
  return 0;
}

/* Set up a binaural sequence */

void
setup_binaural (char *token, void **work)
{
  char *original;
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
  binaural1->last_amp_off1 = binaural1->last_amp_off2 = NULL;  // no previous voice offsets yet
  binaural1->first_pass = 1;  // inactive
  /* used for step and vary */
  binaural1->step_next = NULL;  // default no steps
  binaural1->tot_frames = 0;  // total frames for this step
  binaural1->cur_frames = 0;  // current frames for this step
  binaural1->steps = 0;  // no steps
  binaural1->slide_time = 0.0;  // no slide between steps
  binaural1->fuzz = 0.0;  // no fuzziness around step frequency
  original = StrDup (token);
  str2 = token;

  subtoken = strtok_r (str2, separators, &saveptr2);        // remove voice type
  str2 = NULL;
  
  subtoken = strtok_r (str2, separators, &saveptr2);        // get subtoken of token
  errno = 0;
  double carrier = strtod (subtoken, &endptr);
  if ((carrier == 0.0 && strcmp (subtoken, endptr) == 0) 
      || (*endptr != '\0')
      || errno != 0)
    error ("Carrier for binaural had an error.\n%s\n%s", subtoken, original);
  else if (carrier <= 0.0)  // no errors, but less than equal to zero
    error ("Carrier for binaural cannot be less than or equal to 0.\n%s\n%s", subtoken, original);
  if (opt_m) // modify carrier and beat read from script file
  {
    double band = carrier * modify;  // amount of possible variance
    double adjust = (drand48 ()) * band;  // adjustment amount
    adjust -= (band / 2.);
    carrier += adjust;
  }
  binaural1->carrier = carrier;

  subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
  errno = 0;
  double beat = strtod (subtoken, &endptr);
  if ((beat == 0.0 && strcmp (subtoken, endptr) == 0)
      || (*endptr != '\0')
      || errno != 0)
    error ("Beat for binaural had an error.\n%s\n%s", subtoken, original);
  if (opt_m) // modify carrier and beat read from script file
  {
    double band = (fabs (beat)) * modify;  // amount of possible variance
    double adjust = (drand48 ()) * band;  // adjustment amount
    adjust -= (band / 2.);
    beat += adjust;
  }
  binaural1->beat = beat;

  subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
  errno = 0;
  double amp = strtod (subtoken, &endptr);
  if ((amp == 0.0 && strcmp (subtoken, endptr) == 0)
      || (*endptr != '\0')
      || errno != 0)
    error ("Amplitude for binaural had an error.\n%s\n%s", subtoken, original);
  else if (amp < 0.0)  // no errors, but less than zero
    error ("Amplitude for binaural cannot be less than 0.\n%s\n%s", subtoken, original);
  binaural1->amp = AMP_AD(amp);

  subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
  if (subtoken != NULL && strcmp (subtoken, ">") == 0)  // it's there and slide, done, no amp variation
    binaural1->slide = 1;
  else if (subtoken != NULL && strcmp (subtoken, "&") == 0)  // it's there and step slide, no amp variation
  {
    binaural1->type = 9;  // binaural step
    binaural1->slide = 2;  // binaural step slide

    subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
    errno = 0;
    double steps = strtod (subtoken, &endptr);
    if ((steps == 0.0 && strcmp (subtoken, endptr) == 0)
        || (*endptr != '\0')
        || errno != 0)
      error ("Step count for binaural had an error.\n%s\n%s", subtoken, original);
    else if (steps <= 0.0)  // no errors, but less than equal to zero
      error ("Step count for binaural cannot be less than or equal to 0.\n%s\n%s", subtoken, original);
    binaural1->steps = (int) steps;

    subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
    errno = 0;
    double slide_time = strtod (subtoken, &endptr);
    if ((slide_time == 0.0 && strcmp (subtoken, endptr) == 0)
        || (*endptr != '\0')
        || errno != 0)
      error ("Slide time for binaural had an error.\n%s\n%s", subtoken, original);
    else if (slide_time <= 0.0)  // no errors, but less than equal to zero
      error ("Slide time for binaural cannot be less than or equal to 0.\n%s\n%s", subtoken, original);
    binaural1->slide_time = slide_time;

    subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
    errno = 0;
    double fuzz = strtod (subtoken, &endptr);
    if ((fuzz == 0.0 && strcmp (subtoken, endptr) == 0)
        || (*endptr != '\0')
        || errno != 0)
      error ("Fuzz for binaural had an error.\n%s\n%s", subtoken, original);
    else if (fuzz < 0.0)  // no errors, but less than zero
      error ("Fuzz for binaural cannot be less than 0.\n%s\n%s", subtoken, original);
    binaural1->fuzz = AMP_AD(fuzz);
  }
  else if (subtoken != NULL && strcmp (subtoken, "~") == 0)  // it's there and vary, no amp variation
  {
    binaural1->type = 11;  // binaural vary
    binaural1->slide = 3;  // binaural vary slide

    subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
    errno = 0;
    double steps = strtod (subtoken, &endptr);
    if ((steps == 0.0 && strcmp (subtoken, endptr) == 0)
        || (*endptr != '\0')
        || errno != 0)
      error ("Step count for binaural had an error.\n%s\n%s", subtoken, original);
    else if (steps <= 0.0)  // no errors, but less than equal to zero
      error ("Step count for binaural cannot be less than or equal to 0.\n%s\n%s", subtoken, original);
    binaural1->steps = (int) steps;

    subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
    errno = 0;
    double slide_time = strtod (subtoken, &endptr);
    if ((slide_time == 0.0 && strcmp (subtoken, endptr) == 0)
        || (*endptr != '\0')
        || errno != 0)
      error ("Slide time for binaural had an error.\n%s\n%s", subtoken, original);
    else if (slide_time <= 0.0)  // no errors, but less than equal to zero
      error ("Slide time for binaural cannot be less than or equal to 0.\n%s\n%s", subtoken, original);
    binaural1->slide_time = slide_time;
  }
  else if (subtoken != NULL)  // it's there, not slide, step, or vary, must be amp variation
  {
    errno = 0;
    double amp_beat1 = strtod (subtoken, &endptr);
    if ((amp_beat1 == 0.0 && strcmp (subtoken, endptr) == 0)
        || (*endptr != '\0')
        || errno != 0)
      error ("Amplitude beat1 for binaural had an error.\n%s\n%s", subtoken, original);
    else if (amp_beat1 < 0.0)  // no errors, but less than zero
      error ("Amplitude beat1 for binaural cannot be less than 0.\n%s\n%s", subtoken, original);
    binaural1->amp_beat1 = amp_beat1;

    subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
    errno = 0;
    double amp_beat2 = strtod (subtoken, &endptr);
    if ((amp_beat2 == 0.0 && strcmp (subtoken, endptr) == 0)
        || (*endptr != '\0')
        || errno != 0)
      error ("Amplitude beat2 for binaural had an error.\n%s\n%s", subtoken, original);
    else if (amp_beat2 < 0.0)  // no errors, but less than zero
      error ("Amplitude beat2 for binaural cannot be less than 0.\n%s\n%s", subtoken, original);
    binaural1->amp_beat2 = amp_beat2;

    subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
    errno = 0;
    double amp_pct1 = strtod (subtoken, &endptr);
    if ((amp_pct1 == 0.0 && strcmp (subtoken, endptr) == 0)
        || (*endptr != '\0')
        || errno != 0)
      error ("Amplitude adj1 for binaural had an error.\n%s\n%s", subtoken, original);
    else if (amp_pct1 < 0.0)  // no errors, but less than zero
      error ("Amplitude adj1 for binaural cannot be less than 0.\n%s\n%s", subtoken, original);
    binaural1->amp_pct1 = AMP_AD(amp_pct1);

    subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
    errno = 0;
    double amp_pct2 = strtod (subtoken, &endptr);
    if ((amp_pct2 == 0.0 && strcmp (subtoken, endptr) == 0)
        || (*endptr != '\0')
        || errno != 0)
      error ("Amplitude adj2 for binaural had an error.\n%s\n%s", subtoken, original);
    else if (amp_pct2 < 0.0)  // no errors, but less than zero
      error ("Amplitude adj2 for binaural cannot be less than 0.\n%s\n%s", subtoken, original);
    binaural1->amp_pct2 = AMP_AD(amp_pct2);

    subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
    if (subtoken != NULL && strcmp (subtoken, ">") == 0)  // slide
      binaural1->slide = 1;
    else if (subtoken != NULL && strcmp (subtoken, "&") == 0)  // step slide
    {
      binaural1->type = 9;  // binaural step
      binaural1->slide = 2;  // binaural step slide

      subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
      errno = 0;
      double steps = strtod (subtoken, &endptr);
      if ((steps == 0.0 && strcmp (subtoken, endptr) == 0)
          || (*endptr != '\0')
          || errno != 0)
        error ("Step count for binaural had an error.\n%s\n%s", subtoken, original);
      else if (steps <= 0.0)  // no errors, but less than equal to zero
        error ("Step count for binaural cannot be less than or equal to 0.\n%s\n%s", subtoken, original);
      binaural1->steps = (int) steps;

      subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
      errno = 0;
      double slide_time = strtod (subtoken, &endptr);
      if ((slide_time == 0.0 && strcmp (subtoken, endptr) == 0)
          || (*endptr != '\0')
          || errno != 0)
        error ("Slide time for binaural had an error.\n%s\n%s", subtoken, original);
      else if (slide_time <= 0.0)  // no errors, but less than equal to zero
        error ("Slide time for binaural cannot be less than or equal to 0.\n%s\n%s", subtoken, original);
      binaural1->slide_time = slide_time;

      subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
      errno = 0;
      double fuzz = strtod (subtoken, &endptr);
      if ((fuzz == 0.0 && strcmp (subtoken, endptr) == 0)
          || (*endptr != '\0')
          || errno != 0)
        error ("Fuzz for binaural had an error.\n%s\n%s", subtoken, original);
      else if (fuzz < 0.0)  // no errors, but less than zero
        error ("Fuzz for binaural cannot be less than 0.\n%s\n%s", subtoken, original);
      binaural1->fuzz = AMP_AD(fuzz);
    }
    else if (subtoken != NULL && strcmp (subtoken, "~") == 0)  // vary
    {
      binaural1->type = 11;  // binaural vary
      binaural1->slide = 3;  // binaural vary slide

      subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
      errno = 0;
      double steps = strtod (subtoken, &endptr);
      if ((steps == 0.0 && strcmp (subtoken, endptr) == 0)
          || (*endptr != '\0')
          || errno != 0)
        error ("Step count for binaural had an error.\n%s\n%s", subtoken, original);
      else if (steps <= 0.0)  // no errors, but less than equal to zero
        error ("Step count for binaural cannot be less than or equal to 0.\n%s\n%s", subtoken, original);
      binaural1->steps = (int) steps;

      subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
      errno = 0;
      double slide_time = strtod (subtoken, &endptr);
      if ((slide_time == 0.0 && strcmp (subtoken, endptr) == 0)
          || (*endptr != '\0')
          || errno != 0)
        error ("Slide time for binaural had an error.\n%s\n%s", subtoken, original);
      else if (slide_time <= 0.0)  // no errors, but less than equal to zero
        error ("Slide time for binaural cannot be less than or equal to 0.\n%s\n%s", subtoken, original);
      binaural1->slide_time = slide_time;
    }
    else if (subtoken != NULL) // invalid slide indicator
      error ("Slide indicator for binaural had an error.\n%s\n%s", subtoken, original);
  }
}

/* Set up a bell sequence */

void
setup_bell (char *token, void **work)
{
  char *original;
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
  original = StrDup (token);
  str2 = token;
  subtoken = strtok_r (str2, separators, &saveptr2);        // remove voice type
  str2 = NULL;

  subtoken = strtok_r (str2, separators, &saveptr2);        // get subtoken of token
  errno = 0;
  double carrier = strtod (subtoken, &endptr);
  if ((carrier == 0.0 && strcmp (subtoken, endptr) == 0) 
      || (*endptr != '\0')
      || errno != 0)
    error ("Carrier for bell had an error.\n%s\n%s", subtoken, original);
  else if (carrier <= 0.0)  // no errors, but less than equal to zero
    error ("Carrier for bell cannot be less than or equal to 0.\n%s\n%s", subtoken, original);
  bell1->carrier = carrier;

  subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
  errno = 0;
  double amp_min = strtod (subtoken, &endptr);
  if ((amp_min == 0.0 && strcmp (subtoken, endptr) == 0)
      || (*endptr != '\0')
      || errno != 0)
    error ("Minimum amplitude for bell had an error.\n%s\n%s", subtoken, original);
  else if (amp_min < 0.0 || amp_min > 100.0)  // no errors, but less than zero, greater than 100
    error ("Minimum amplitude for bell cannot be less than 0 or greater than 100.\n%s\n%s", subtoken, original);
  bell1->amp_min = AMP_AD(amp_min);

  subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
  errno = 0;
  double amp_max = strtod (subtoken, &endptr);
  if ((amp_max == 0.0 && strcmp (subtoken, endptr) == 0)
      || (*endptr != '\0')
      || errno != 0)
    error ("Maximum amplitude for bell had an error.\n%s\n%s", subtoken, original);
  else if (amp_max < amp_min || amp_max > 100.0)  // no errors, but less than amp_min, greater than 100
    error ("Maximum amplitude for bell cannot be less than minimum amplitude or greater than 100.\n%s\n%s", subtoken, original);
  bell1->amp_max = AMP_AD(amp_max);

  subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
  errno = 0;
  double split_begin = strtod (subtoken, &endptr);
  if ((split_begin == 0.0 && strcmp (subtoken, endptr) == 0)
      || (*endptr != '\0')
      || errno != 0)
    error ("Beginning split for bell had an error.\n%s\n%s", subtoken, original);
  else if ((split_begin < 0.0 && split_begin != -1.0) || split_begin > 1.0)  // no errors, but less than zero, greater than 1
    error ("Beginning split for bell cannot be less than 0 except for -1, or greater than 1.\n%s\n%s", subtoken, original);
  bell1->split_begin = split_begin;

  subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
  errno = 0;
  double split_end = strtod (subtoken, &endptr);
  if ((split_end == 0.0 && strcmp (subtoken, endptr) == 0)
      || (*endptr != '\0')
      || errno != 0)
    error ("Ending split for bell had an error.\n%s\n%s", subtoken, original);
  else if ((split_end < 0.0 && split_end != -1.0) || split_end > 1.0)  // no errors, but less than zero, greater than 1
    error ("Ending split for bell cannot be less than 0 except for -1, or greater than 1.\n%s\n%s", subtoken, original);
  bell1->split_end = split_end;

  subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
  errno = 0;
  double split_low = strtod (subtoken, &endptr);
  if ((split_low == 0.0 && strcmp (subtoken, endptr) == 0)
      || (*endptr != '\0')
      || errno != 0)
    error ("Low split limit for bell had an error.\n%s\n%s", subtoken, original);
  else if (split_low < 0.0 || split_low > 1.0)  // no errors, but less than zero, greater than 1
    error ("Low split limit for bell cannot be less than 0 or greater than 1.\n%s\n%s", subtoken, original);
  bell1->split_low = split_low;

  subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
  errno = 0;
  double split_high = strtod (subtoken, &endptr);
  if ((split_high == 0.0 && strcmp (subtoken, endptr) == 0)
      || (*endptr != '\0')
      || errno != 0)
    error ("High split limit for bell had an error.\n%s\n%s", subtoken, original);
  else if (split_high < split_low || split_high > 1.0)  // no errors, but less than split_low or greater than 1
    error ("High split limit for bell cannot be less than low split limit or greater than 1.\n%s\n%s", subtoken, original);
  bell1->split_high = split_high;

  subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
  errno = 0;
  double length_min = strtod (subtoken, &endptr);
  if ((length_min == 0.0 && strcmp (subtoken, endptr) == 0)
      || (*endptr != '\0')
      || errno != 0)
    error ("Minimum time for bell had an error.\n%s\n%s", subtoken, original);
  else if (length_min < 0.0)  // no errors, but less than 0
    error ("Minimum time for bell cannot be less than 0.\n%s\n%s", subtoken, original);
  bell1->length_min = (int_64) (length_min * out_rate);      // convert to frames from seconds

  subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
  errno = 0;
  double length_max = strtod (subtoken, &endptr);
  if ((length_max == 0.0 && strcmp (subtoken, endptr) == 0)
      || (*endptr != '\0')
      || errno != 0)
    error ("Maximum time for bell had an error.\n%s\n%s", subtoken, original);
  else if (length_max < length_min)  // no errors, but less than minimum time
    error ("Maximum time for bell cannot be less than minimum time.\n%s\n%s", subtoken, original);
  bell1->length_max = (int_64) (length_max * out_rate);      // convert to frames from seconds

  subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
  errno = 0;
  double repeat_min = strtod (subtoken, &endptr);
  if ((repeat_min == 0.0 && strcmp (subtoken, endptr) == 0)
      || (*endptr != '\0')
      || errno != 0)
    error ("Minimum repeat interval for bell had an error.\n%s\n%s", subtoken, original);
  else if (repeat_min < 0.0)  // no errors, but less than 0
    error ("Minimum repeat interval for bell cannot be less than 0.\n%s\n%s", subtoken, original);
  bell1->repeat_min = (int_64) (repeat_min * out_rate);      // convert to frames from seconds

  subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
  errno = 0;
  double repeat_max = strtod (subtoken, &endptr);
  if ((repeat_max == 0.0 && strcmp (subtoken, endptr) == 0)
      || (*endptr != '\0')
      || errno != 0)
    error ("Maximum repeat interval for bell had an error.\n%s\n%s", subtoken, original);
  else if (repeat_max < repeat_min)  // no errors, but less than min repeat interval
    error ("Maximum repeat interval for bell cannot be less than minimum repeat interval.\n%s\n%s", subtoken, original);
  bell1->repeat_max = (int_64) (repeat_max * out_rate);      // convert to frames from seconds

  subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
  errno = 0;
  double behave = strtod (subtoken, &endptr);
  if ((behave == 0.0 && strcmp (subtoken, endptr) == 0)
      || (*endptr != '\0')
      || errno != 0)
    error ("Tone behavior for bell had an error.\n%s\n%s", subtoken, original);
  else if (behave < 1.0 || behave > 5.0)  // no errors, but outside behavior range
    error ("Tone behavior for bell cannot be less than 1 or greater than 5.\n%s\n%s", subtoken, original);
  bell1->behave = (int) behave;   // convert to int

  /* create the time to first play of bell */
  if (bell1->repeat_min == bell1->repeat_max)
    // fixed period, start immediately
    bell1->next_play = 0LL;
  else
  {
      // frames to next play random piece of possible interval
    int_64 delta = (int_64) ( (drand48 ()) * (bell1->repeat_max - bell1->repeat_min));
    bell1->next_play = delta/2;  // bias towards sooner
  }
  bell1->sofar = 0LL;
}

/* Set up a noise sequence */

int
setup_noise (char *token, void **work)
{
  char *original;
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
  original = StrDup (token);
  str2 = token;
  subtoken = strtok_r (str2, separators, &saveptr2);        // remove voice type
  str2 = NULL;

  subtoken = strtok_r (str2, separators, &saveptr2);        // get subtoken of token
  errno = 0;
  double carrier_min = strtod (subtoken, &endptr);
  if ((carrier_min == 0.0 && strcmp (subtoken, endptr) == 0) 
      || (*endptr != '\0')
      || errno != 0)
    error ("Minimum carrier for noise had an error.\n%s\n%s", subtoken, original);
  else if (carrier_min <= 0.0)  // no errors, but less than equal to zero
    error ("Minimum carrier for noise cannot be less than or equal to 0.\n%s\n%s", subtoken, original);
  noise1->carrier_min = carrier_min;
  
  subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
  errno = 0;
  double carrier_max = strtod (subtoken, &endptr);
  if ((carrier_max == 0.0 && strcmp (subtoken, endptr) == 0) 
      || (*endptr != '\0')
      || errno != 0)
    error ("Maximum carrier for noise had an error.\n%s\n%s", subtoken, original);
  else if (carrier_max < carrier_min)  // no errors, but less than carrier min
    error ("Maximum carrier for noise cannot be less than minimum carrier.\n%s\n%s", subtoken, original);
  noise1->carrier_max = carrier_max;

  subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
  errno = 0;
  double amp_min = strtod (subtoken, &endptr);
  if ((amp_min == 0.0 && strcmp (subtoken, endptr) == 0) 
      || (*endptr != '\0')
      || errno != 0)
    error ("Minimum amplitude for noise had an error.\n%s\n%s", subtoken, original);
  else if (amp_min <= 0.0)  // no errors, but less than equal to zero
    error ("Minimum amplitude for noise cannot be less than or equal to 0.\n%s\n%s", subtoken, original);
  noise1->amp_min = AMP_AD(amp_min);

  subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
  errno = 0;
  double amp_max = strtod (subtoken, &endptr);
  if ((amp_max == 0.0 && strcmp (subtoken, endptr) == 0) 
      || (*endptr != '\0')
      || errno != 0)
    error ("Maximum amplitude for noise had an error.\n%s\n%s", subtoken, original);
  else if (amp_max < amp_min)  // no errors, but less than minimum amplitude
    error ("Maximum amplitude for noise cannot be less than maximum amplitude.\n%s\n%s", subtoken, original);
  noise1->amp_max = AMP_AD(amp_max);

  subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
  errno = 0;
  double split_begin = strtod (subtoken, &endptr);
  if ((split_begin == 0.0 && strcmp (subtoken, endptr) == 0)
      || (*endptr != '\0')
      || errno != 0)
    error ("Beginning split for noise had an error.\n%s\n%s", subtoken, original);
  else if ((split_begin < 0.0 && split_begin != -1.0) || split_begin > 1.0)  // no errors, but less than zero, greater than 1
    error ("Beginning split for noise cannot be less than 0 except for -1, or greater than 1.\n%s\n%s", subtoken, original);
  noise1->split_begin = split_begin;

  subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
  errno = 0;
  double split_end = strtod (subtoken, &endptr);
  if ((split_end == 0.0 && strcmp (subtoken, endptr) == 0)
      || (*endptr != '\0')
      || errno != 0)
    error ("Ending split for noise had an error.\n%s\n%s", subtoken, original);
  else if ((split_end < 0.0 && split_end != -1.0) || split_end > 1.0)  // no errors, but less than zero, greater than 1
    error ("Ending split for noise cannot be less than 0 except for -1, or greater than 1.\n%s\n%s", subtoken, original);
  noise1->split_end = split_end;

  subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
  errno = 0;
  double split_low = strtod (subtoken, &endptr);
  if ((split_low == 0.0 && strcmp (subtoken, endptr) == 0)
      || (*endptr != '\0')
      || errno != 0)
    error ("Low split limit for noise had an error.\n%s\n%s", subtoken, original);
  else if (split_low < 0.0 || split_low > 1.0)  // no errors, but less than zero, greater than 1
    error ("Low split limit for noise cannot be less than 0 or greater than 1.\n%s\n%s", subtoken, original);
  noise1->split_low = split_low;

  subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
  errno = 0;
  double split_high = strtod (subtoken, &endptr);
  if ((split_high == 0.0 && strcmp (subtoken, endptr) == 0)
      || (*endptr != '\0')
      || errno != 0)
    error ("High split limit for noise had an error.\n%s\n%s", subtoken, original);
  else if (split_high < split_low || split_high > 1.0)  // no errors, but less than split_low or greater than 1
    error ("High split limit for noise cannot be less than low split limit or greater than 1.\n%s\n%s", subtoken, original);
  noise1->split_high = split_high;

  subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
  errno = 0;
  double length_min = strtod (subtoken, &endptr);
  if ((length_min == 0.0 && strcmp (subtoken, endptr) == 0)
      || (*endptr != '\0')
      || errno != 0)
    error ("Minimum time for noise had an error.\n%s\n%s", subtoken, original);
  else if (length_min < 0.0)  // no errors, but less than 0
    error ("Minimum time for noise cannot be less than 0.\n%s\n%s", subtoken, original);
  noise1->length_min = (int_64) (length_min * out_rate);      // convert to frames from seconds

  subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
  errno = 0;
  double length_max = strtod (subtoken, &endptr);
  if ((length_max == 0.0 && strcmp (subtoken, endptr) == 0)
      || (*endptr != '\0')
      || errno != 0)
    error ("Maximum time for noise had an error.\n%s\n%s", subtoken, original);
  else if (length_max < length_min)  // no errors, but less than minimum time
    error ("Maximum time for noise cannot be less than minimum time.\n%s\n%s", subtoken, original);
  noise1->length_max = (int_64) (length_max * out_rate);      // convert to frames from seconds

  subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
  errno = 0;
  double repeat_min = strtod (subtoken, &endptr);
  if ((repeat_min == 0.0 && strcmp (subtoken, endptr) == 0)
      || (*endptr != '\0')
      || errno != 0)
    error ("Minimum repeat interval for noise had an error.\n%s\n%s", subtoken, original);
  else if (repeat_min < 0.0)  // no errors, but less than 0
    error ("Minimum repeat interval for noise cannot be less than 0.\n%s\n%s", subtoken, original);
  noise1->repeat_min = (int_64) (repeat_min * out_rate);      // convert to frames from seconds

  subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
  errno = 0;
  double repeat_max = strtod (subtoken, &endptr);
  if ((repeat_max == 0.0 && strcmp (subtoken, endptr) == 0)
      || (*endptr != '\0')
      || errno != 0)
    error ("Maximum repeat interval for noise had an error.\n%s\n%s", subtoken, original);
  else if (repeat_max < repeat_min)  // no errors, but less than min repeat interval
    error ("Maximum repeat interval for noise cannot be less than minimum repeat interval.\n%s\n%s", subtoken, original);
  noise1->repeat_max = (int_64) (repeat_max * out_rate);      // convert to frames from seconds

  subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
  errno = 0;
  double behave_low = strtod (subtoken, &endptr);
  if ((behave_low == 0.0 && strcmp (subtoken, endptr) == 0)
      || (*endptr != '\0')
      || errno != 0)
    error ("Tone behavior lower limit for noise had an error.\n%s\n%s", subtoken, original);
  else if (behave_low < 1.0 || behave_low > 21.0)  // no errors, but outside behavior range
    error ("Tone behavior lower limit for noise cannot be less than 1 or greater than 21.\n%s\n%s", subtoken, original);
  noise1->behave_low = (int) behave_low;   // convert to int

  subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
  errno = 0;
  double behave_high = strtod (subtoken, &endptr);
  if ((behave_high == 0.0 && strcmp (subtoken, endptr) == 0)
      || (*endptr != '\0')
      || errno != 0)
    error ("Tone behavior upper limit for noise had an error.\n%s\n%s", subtoken, original);
  else if (behave_high < behave_low || behave_high > 21.0)  // no errors, but outside behavior range
    error ("Tone behavior upper limit for noise cannot be less than lower limit, greater than 21.\n%s\n%s", subtoken, original);
  noise1->behave_high = (int) behave_high;         // convert to int

    /* possible multiplier for a noise voice */
  subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
  double multiple = 0.0;
  if (subtoken)  // not null
  {
    errno = 0;
    multiple = strtod (subtoken, &endptr);
    if ((multiple == 0.0 && strcmp (subtoken, endptr) == 0)
        || (*endptr != '\0')
        || errno != 0)
      error ("Multiplier for noise had an error.\n%s\n%s", subtoken, original);
    else if (multiple < 1.0)  // no errors, but less than 1
      error ("Multiplier for noise cannot be less than 1.\n%s\n%s", subtoken, original);
  }
  else
    multiple = 1.0;
  /* create the time to first play of noise */
  if (noise1->repeat_min == noise1->repeat_max)
    // fixed period, random start
    noise1->next_play = (int_64) (drand48() * noise1->repeat_min);
  else
  {
      // frames to next play random piece of possible interval
    int_64 delta = (int_64) ( (drand48 ()) * (noise1->repeat_max - noise1->repeat_min));
    noise1->next_play = delta;      // frames to next play
  }
  noise1->sofar = noise1->next_play;  // immediate start
  return abs ((int) multiple);         // convert to int
}

/* Set up a stoch file sequence */

void
setup_stoch (char *token, void **work)
{
  char *original;
  char *endptr;
  char *subtoken;
  char *str2 = NULL;
  char *saveptr2;
  char filename [256];
  stoch *stoch1 = NULL;
  snd_buffer *sb1 = NULL;

  stoch1 = (stoch *) Alloc (sizeof (stoch) * 1);
  *work = stoch1;
  stoch1->next = NULL;
  stoch1->type = 4;
  stoch1->off1 = 0;
  original = StrDup (token);
  str2 = token;
  subtoken = strtok_r (str2, separators, &saveptr2);        // remove voice type
  str2 = NULL;
  subtoken = strtok_r (str2, separators, &saveptr2);        // get subtoken of token
  /* subtoken is file name for stoch sound */
  strcpy (filename, subtoken);
  sb1 = process_sound_file (filename);
  stoch1->channels = sb1->channels;
  stoch1->mono = sb1->mono;
  stoch1->frames = sb1->frames;
  stoch1->sound = sb1->sound;
  stoch1->scale = sb1->scale;
                                    
  subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
  errno = 0;
  double amp_min = strtod (subtoken, &endptr);
  if ((amp_min == 0.0 && strcmp (subtoken, endptr) == 0)
      || (*endptr != '\0')
      || errno != 0)
    error ("Minimum amplitude for stoch had an error.\n%s\n%s", subtoken, original);
  else if (amp_min < 0.0 || amp_min > 100.0)  // no errors, but less than zero, greater than 100
    error ("Minimum amplitude for stoch cannot be less than 0 or greater than 100.\n%s\n%s", subtoken, original);
  stoch1->amp_min = AMP_AD(amp_min);

  subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
  errno = 0;
  double amp_max = strtod (subtoken, &endptr);
  if ((amp_max == 0.0 && strcmp (subtoken, endptr) == 0)
      || (*endptr != '\0')
      || errno != 0)
    error ("Maximum amplitude for stoch had an error.\n%s\n%s", subtoken, original);
  else if (amp_max < amp_min || amp_max > 100.0)  // no errors, but less than amp_min, greater than 100
    error ("Maximum amplitude for stoch cannot be less than minimum amplitude or greater than 100.\n%s\n%s", 
                                                                subtoken, original);
  stoch1->amp_max = AMP_AD(amp_max);

  subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
  errno = 0;
  double split_begin = strtod (subtoken, &endptr);
  if ((split_begin == 0.0 && strcmp (subtoken, endptr) == 0) 
      || (*endptr != '\0')
      || errno != 0)
    error ("Beginning split for stoch had an error.\n%s\n%s", subtoken, original);
  else if ((split_begin < 0.0 && split_begin != -1.0) || split_begin > 1.0)  // no errors, but less than zero, greater than 1
    error ("Beginning split for stoch cannot be less than 0 except for -1, or greater than 1.\n%s\n%s", subtoken, original);
  stoch1->split_begin = split_begin;

  subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
  errno = 0;
  double split_end = strtod (subtoken, &endptr);
  if ((split_end == 0.0 && strcmp (subtoken, endptr) == 0)
      || (*endptr != '\0')
      || errno != 0)
    error ("Ending split for stoch had an error.\n%s\n%s", subtoken, original);
  else if ((split_end < 0.0 && split_end != -1.0) || split_end > 1.0)  // no errors, but less than zero, greater than 1
    error ("Ending split for stoch cannot be less than 0 except for -1, or greater than 1.\n%s\n%s", subtoken, original);
  stoch1->split_end = split_end;

  subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
  errno = 0;
  double split_low = strtod (subtoken, &endptr);
  if ((split_low == 0.0 && strcmp (subtoken, endptr) == 0)
      || (*endptr != '\0')
      || errno != 0)
    error ("Low split limit for stoch had an error.\n%s\n%s", subtoken, original);
  else if (split_low < 0.0 || split_low > 1.0)  // no errors, but less than zero, greater than 1
    error ("Low split limit for stoch cannot be less than 0 or greater than 1.\n%s\n%s", subtoken, original);
  stoch1->split_low = split_low;

  subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
  errno = 0;
  double split_high = strtod (subtoken, &endptr);
  if ((split_high == 0.0 && strcmp (subtoken, endptr) == 0)
      || (*endptr != '\0')
      || errno != 0)
    error ("High split limit for stoch had an error.\n%s\n%s", subtoken, original);
  else if (split_high < split_low || split_high > 1.0)  // no errors, but less than split_low or greater than 1
    error ("High split limit for stoch cannot be less than low split limit or greater than 1.\n%s\n%s", subtoken, original);
  stoch1->split_high = split_high;

  subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
  errno = 0;
  double repeat_min = strtod (subtoken, &endptr);
  if ((repeat_min == 0.0 && strcmp (subtoken, endptr) == 0)
      || (*endptr != '\0')
      || errno != 0)
    error ("Minimum repeat interval for stoch had an error.\n%s\n%s", subtoken, original);
  else if (repeat_min < 0.0)  // no errors, but less than 0
    error ("Minimum repeat interval for stoch cannot be less than 0.\n%s\n%s", subtoken, original);
  stoch1->repeat_min = (int_64) (repeat_min * out_rate);      // convert to frames from seconds

  subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
  errno = 0;
  double repeat_max = strtod (subtoken, &endptr);
  if ((repeat_max == 0.0 && strcmp (subtoken, endptr) == 0)
      || (*endptr != '\0')
      || errno != 0)
    error ("Maximum repeat interval for stoch had an error.\n%s\n%s", subtoken, original);
  else if (repeat_max < repeat_min)  // no errors, but less than min repeat interval
    error ("Maximum repeat interval for stoch cannot be less than minimum repeat interval.\n%s\n%s", subtoken, original);
  stoch1->repeat_max = (int_64) (repeat_max * out_rate);      // convert to frames from seconds

  /* set up frames till first play of stoch */
  if (stoch1->repeat_min == stoch1->repeat_max)
  {
    stoch1->next_play = stoch1->repeat_min;      // fixed period, start at repeat interval
  }
  else
  {
    stoch1->next_play  = (int_64) ( (drand48 ()) * stoch1->repeat_max);  // random up to max repeat interval
  }
  stoch1->sofar = 0LL;
}

/* Set up a sample file sequence */

void
setup_sample (char *token, void **work)
{
  char *original;
  char *endptr;
  char *subtoken;
  char *str2 = NULL;
  char *saveptr2;
  char filename [256];
  sample *sample1 = NULL;
  snd_buffer *sb1 = NULL;

  sample1 = (sample *) Alloc (sizeof (sample) * 1);
  *work = sample1;
  sample1->next = NULL;
  sample1->type = 5;
  original = StrDup (token);
  str2 = token;
  subtoken = strtok_r (str2, separators, &saveptr2);        // remove voice type
  str2 = NULL;
  subtoken = strtok_r (str2, separators, &saveptr2);        // get subtoken of token
  /* subtoken is file name for sample sound */
  strcpy (filename, subtoken);
  sb1 = process_sound_file (filename);
  sample1->channels = sb1->channels;
  sample1->mono = sb1->mono;
  sample1->frames = sb1->frames;
  sample1->sound = sb1->sound;
  sample1->scale = sb1->scale;
                                    
  subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
  errno = 0;
  double amp_min = strtod (subtoken, &endptr);
  if ((amp_min == 0.0 && strcmp (subtoken, endptr) == 0)
      || (*endptr != '\0')
      || errno != 0)
    error ("Minimum amplitude for sample had an error.\n%s\n%s", subtoken, original);
  else if (amp_min < 0.0 || amp_min > 100.0)  // no errors, but less than zero, greater than 100
    error ("Minimum amplitude for sample cannot be less than 0 or greater than 100.\n%s\n%s", subtoken, original);
  sample1->amp_min = AMP_AD(amp_min);

  subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
  errno = 0;
  double amp_max = strtod (subtoken, &endptr);
  if ((amp_max == 0.0 && strcmp (subtoken, endptr) == 0)
      || (*endptr != '\0')
      || errno != 0)
    error ("Maximum amplitude for sample had an error.\n%s\n%s", subtoken, original);
  else if (amp_max < amp_min || amp_max > 100.0)  // no errors, but less than amp_min, greater than 100
    error ("Maximum amplitude for sample cannot be less than minimum amplitude or greater than 100.\n%s\n%s", 
                                                                 subtoken, original);
  sample1->amp_max = AMP_AD(amp_max);

  subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
  errno = 0;
  double split_begin = strtod (subtoken, &endptr);
  if ((split_begin == 0.0 && strcmp (subtoken, endptr) == 0)
      || (*endptr != '\0')
      || errno != 0)
    error ("Beginning split for sample had an error.\n%s\n%s", subtoken, original);
  else if ((split_begin < 0.0 && split_begin != -1.0) || split_begin > 1.0)  // no errors, but less than zero, greater than 1
    error ("Beginning split for sample cannot be less than 0 except for -1, or greater than 1.\n%s\n%s", subtoken, original);
  sample1->split_begin = split_begin;

  subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
  errno = 0;
  double split_end = strtod (subtoken, &endptr);
  if ((split_end == 0.0 && strcmp (subtoken, endptr) == 0)
      || (*endptr != '\0')
      || errno != 0)
    error ("Ending split for sample had an error.\n%s\n%s", subtoken, original);
  else if ((split_end < 0.0 && split_end != -1.0) || split_end > 1.0)  // no errors, but less than zero, greater than 1
    error ("Ending split for sample cannot be less than 0 except for -1, or greater than 1.\n%s\n%s", subtoken, original);
  sample1->split_end = split_end;

  subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
  errno = 0;
  double split_low = strtod (subtoken, &endptr);
  if ((split_low == 0.0 && strcmp (subtoken, endptr) == 0)
      || (*endptr != '\0')
      || errno != 0)
    error ("Low split limit for sample had an error.\n%s\n%s", subtoken, original);
  else if (split_low < 0.0 || split_low > 1.0)  // no errors, but less than zero, greater than 1
    error ("Low split limit for sample cannot be less than 0 or greater than 1.\n%s\n%s", subtoken, original);
  sample1->split_low = split_low;

  subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
  errno = 0;
  double split_high = strtod (subtoken, &endptr);
  if ((split_high == 0.0 && strcmp (subtoken, endptr) == 0)
      || (*endptr != '\0')
      || errno != 0)
    error ("High split limit for sample had an error.\n%s\n%s", subtoken, original);
  else if (split_high < split_low || split_high > 1.0)  // no errors, but less than split_low or greater than 1
    error ("High split limit for sample cannot be less than low split limit or greater than 1.\n%s\n%s", subtoken, original);
  sample1->split_high = split_high;

  subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
  errno = 0;
  double sample_size = strtod (subtoken, &endptr);
  if ((sample_size == 0.0 && strcmp (subtoken, endptr) == 0)
      || (*endptr != '\0')
      || errno != 0)
    error ("Sample size for sample had an error.\n%s\n%s", subtoken, original);
  else if (sample_size < 0.0)  // no errors, but less than zero
    error ("Sample size for sample cannot be less than 0.\n%s\n%s", subtoken, original);
  sample1->size = (int_64) (sample_size * out_rate);  // convert from seconds to frames 

  /* Set some defaults so sample position is determined randomly at start of generate frames */
  sample1->play = 0LL;  // start out with zero play size, let generate frames determine
  sample1->off1 = 0LL;  // set in generate frames when play is zero.
}

/* Set up a repeat file sequence */

void
setup_repeat (char *token, void **work)
{
  char *original;
  char *endptr;
  char *subtoken;
  char *str2 = NULL;
  char *saveptr2;
  char filename [256];
  repeat *repeat1 = NULL;
  snd_buffer *sb1 = NULL;

  repeat1 = (repeat *) Alloc (sizeof (repeat) * 1);
  *work = repeat1;
  repeat1->next = NULL;
  repeat1->type = 6;
  original = StrDup (token);
  str2 = token;
  subtoken = strtok_r (str2, separators, &saveptr2);        // remove voice type
  str2 = NULL;
  subtoken = strtok_r (str2, separators, &saveptr2);        // get subtoken of token
  /* subtoken is file name for repeat sound */
  strcpy (filename, subtoken);
  sb1 = process_sound_file (filename);
  repeat1->channels = sb1->channels;
  repeat1->mono = sb1->mono;
  repeat1->frames = sb1->frames;
  repeat1->sound = sb1->sound;
  repeat1->scale = sb1->scale;
                                    
  subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
  errno = 0;
  double amp_min = strtod (subtoken, &endptr);
  if ((amp_min == 0.0 && strcmp (subtoken, endptr) == 0)
      || (*endptr != '\0')
      || errno != 0)
    error ("Minimum amplitude for repeat had an error.\n%s\n%s", subtoken, original);
  else if (amp_min < 0.0 || amp_min > 100.0)  // no errors, but less than zero, greater than 100
    error ("Minimum amplitude for repeat cannot be less than 0 or greater than 100.\n%s\n%s", subtoken, original);
  repeat1->amp_min = AMP_AD(amp_min);

  subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
  errno = 0;
  double amp_max = strtod (subtoken, &endptr);
  if ((amp_max == 0.0 && strcmp (subtoken, endptr) == 0)
      || (*endptr != '\0')
      || errno != 0)
    error ("Maximum amplitude for repeat had an error.\n%s\n%s", subtoken, original);
  else if (amp_max < amp_min || amp_max > 100.0)  // no errors, but less than amp_min, greater than 100
    error ("Maximum amplitude for repeat cannot be less than minimum amplitude or greater than 100.\n%s\n%s", 
                                                                 subtoken, original);
  repeat1->amp_max = AMP_AD(amp_max);

  subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
  errno = 0;
  double split_begin = strtod (subtoken, &endptr);
  if ((split_begin == 0.0 && strcmp (subtoken, endptr) == 0)
      || (*endptr != '\0')
      || errno != 0)
    error ("Beginning split for repeat had an error.\n%s\n%s", subtoken, original);
  else if ((split_begin < 0.0 && split_begin != -1.0) || split_begin > 1.0)  // no errors, but less than zero, greater than 1
    error ("Beginning split for repeat cannot be less than 0 except for -1, or greater than 1.\n%s\n%s", subtoken, original);
  repeat1->split_begin = split_begin;

  subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
  errno = 0;
  double split_end = strtod (subtoken, &endptr);
  if ((split_end == 0.0 && strcmp (subtoken, endptr) == 0)
      || (*endptr != '\0')
      || errno != 0)
    error ("Ending split for repeat had an error.\n%s\n%s", subtoken, original);
  else if ((split_end < 0.0 && split_end != -1.0) || split_end > 1.0)  // no errors, but less than zero, greater than 1
    error ("Ending split for repeat cannot be less than 0 except for -1, or greater than 1.\n%s\n%s", subtoken, original);
  repeat1->split_end = split_end;

  subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
  errno = 0;
  double split_low = strtod (subtoken, &endptr);
  if ((split_low == 0.0 && strcmp (subtoken, endptr) == 0)
      || (*endptr != '\0')
      || errno != 0)
    error ("Low split limit for repeat had an error.\n%s\n%s", subtoken, original);
  else if (split_low < 0.0 || split_low > 1.0)  // no errors, but less than zero, greater than 1
    error ("Low split limit for repeat cannot be less than 0 or greater than 1.\n%s\n%s", subtoken, original);
  repeat1->split_low = split_low;

  subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
  errno = 0;
  double split_high = strtod (subtoken, &endptr);
  if ((split_high == 0.0 && strcmp (subtoken, endptr) == 0)
      || (*endptr != '\0')
      || errno != 0)
    error ("High split limit for repeat had an error.\n%s\n%s", subtoken, original);
  else if (split_high < split_low || split_high > 1.0)  // no errors, but less than split_low or greater than 1
    error ("High split limit for repeat cannot be less than low split limit or greater than 1.\n%s\n%s", subtoken, original);
  repeat1->split_high = split_high;

  /* set play to initialize in generate frames */
  repeat1->play = 0LL;  // how much has played so far
}

/* Set up a once file sequence */

void
setup_once (char *token, void **work)
{
  char *original;
  char *endptr;
  char *subtoken;
  char *str2 = NULL;
  char *saveptr2;
  char filename [256];
  once *once1 = NULL;
  snd_buffer *sb1 = NULL;

  once1 = (once *) Alloc (sizeof (once) * 1);
  *work = once1;
  once1->next = NULL;
  once1->type = 7;
  once1->off1 = 0;
  once1->not_played = 1;  // haven't played yed
  original = StrDup (token);
  str2 = token;
  subtoken = strtok_r (str2, separators, &saveptr2);        // remove voice type
  str2 = NULL;
  subtoken = strtok_r (str2, separators, &saveptr2);        // get subtoken of token
  /* subtoken is file name for once sound */
  strcpy (filename, subtoken);
  sb1 = process_sound_file (filename);
  once1->channels = sb1->channels;
  once1->mono = sb1->mono;
  once1->frames = sb1->frames;
  once1->sound = sb1->sound;
  once1->scale = sb1->scale;
                                    
  subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
  errno = 0;
  double amp_min = strtod (subtoken, &endptr);
  if ((amp_min == 0.0 && strcmp (subtoken, endptr) == 0)
      || (*endptr != '\0')
      || errno != 0)
    error ("Minimum amplitude for once had an error.\n%s\n%s", subtoken, original);
  else if (amp_min < 0.0 || amp_min > 100.0)  // no errors, but less than zero, greater than 100
    error ("Minimum amplitude for once cannot be less than 0 or greater than 100.\n%s\n%s", subtoken, original);
  once1->amp_min = AMP_AD(amp_min);

  subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
  errno = 0;
  double amp_max = strtod (subtoken, &endptr);
  if ((amp_max == 0.0 && strcmp (subtoken, endptr) == 0)
      || (*endptr != '\0')
      || errno != 0)
    error ("Maximum amplitude for once had an error.\n%s\n%s", subtoken, original);
  else if (amp_max < amp_min || amp_max > 100.0)  // no errors, but less than amp_min, greater than 100
    error ("Maximum amplitude for once cannot be less than minimum amplitude or greater than 100.\n%s\n%s", subtoken, original);
  once1->amp_max = AMP_AD(amp_max);

  subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
  errno = 0;
  double split_begin = strtod (subtoken, &endptr);
  if ((split_begin == 0.0 && strcmp (subtoken, endptr) == 0)
      || (*endptr != '\0')
      || errno != 0)
    error ("Beginning split for once had an error.\n%s\n%s", subtoken, original);
  else if ((split_begin < 0.0 && split_begin != -1.0) || split_begin > 1.0)  // no errors, but less than zero, greater than 1
    error ("Beginning split for once cannot be less than 0 except for -1, or greater than 1.\n%s\n%s", subtoken, original);
  once1->split_begin = split_begin;

  subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
  errno = 0;
  double split_end = strtod (subtoken, &endptr);
  if ((split_end == 0.0 && strcmp (subtoken, endptr) == 0)
      || (*endptr != '\0')
      || errno != 0)
    error ("Ending split for once had an error.\n%s\n%s", subtoken, original);
  else if ((split_end < 0.0 && split_end != -1.0) || split_end > 1.0)  // no errors, but less than zero, greater than 1
    error ("Ending split for once cannot be less than 0 except for -1, or greater than 1.\n%s\n%s", subtoken, original);
  once1->split_end = split_end;

  subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
  errno = 0;
  double split_low = strtod (subtoken, &endptr);
  if ((split_low == 0.0 && strcmp (subtoken, endptr) == 0)
      || (*endptr != '\0')
      || errno != 0)
    error ("Low split limit for once had an error.\n%s\n%s", subtoken, original);
  else if (split_low < 0.0 || split_low > 1.0)  // no errors, but less than zero, greater than 1
    error ("Low split limit for once cannot be less than 0 or greater than 1.\n%s\n%s", subtoken, original);
  once1->split_low = split_low;

  subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
  errno = 0;
  double split_high = strtod (subtoken, &endptr);
  if ((split_high == 0.0 && strcmp (subtoken, endptr) == 0)
      || (*endptr != '\0')
      || errno != 0)
    error ("High split limit for once had an error.\n%s\n%s", subtoken, original);
  else if (split_high < split_low || split_high > 1.0)  // no errors, but less than split_low or greater than 1
    error ("High split limit for once cannot be less than low split limit or greater than 1.\n%s\n%s", subtoken, original);
  once1->split_high = split_high;

  subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
  errno = 0;
  double play_when = strtod (subtoken, &endptr);
  if ((play_when == 0.0 && strcmp (subtoken, endptr) == 0)
      || (*endptr != '\0')
      || errno != 0)
    error ("Play time for once had an error.\n%s\n%s", subtoken, original);
  else if (play_when < 0.0)  // no errors, but less than 0
    error ("Play time for once cannot be less than 0.\n%s\n%s", subtoken, original);
  once1->play_when = (int_64) (play_when * out_rate);      // convert to frames from seconds

  /* set up play of once */
  once1->sofar = once1->play = (int_64) 0;
}

/* Set up a chronaural sequence */

void
setup_chronaural (char *token, void **work)
{
  char *original;
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
  chronaural1->off1 = chronaural1->off3 = chronaural1->off2 = 0;  // begin at 0 degrees
  chronaural1->last_off1 = chronaural1->last_off3 = chronaural1->last_off2 = NULL;  // no previous voice offsets yet
  chronaural1->first_pass = 1;  // inactive
  /* used for step and vary */
  chronaural1->step_next = NULL;  // default no steps
  chronaural1->tot_frames = 0;  // total frames for this step
  chronaural1->cur_frames = 0;  // current frames for this step
  chronaural1->steps = 0;  // no steps
  chronaural1->slide_time = 0.0;  // no slide between steps
  chronaural1->fuzz = 0.0;  // no fuzziness around step frequency
  original = StrDup (token);
  str2 = token;

  subtoken = strtok_r (str2, separators, &saveptr2);        // remove voice type
  str2 = NULL;
  
  subtoken = strtok_r (str2, separators, &saveptr2);        // get subtoken of token
  errno = 0;
  double carrier = strtod (subtoken, &endptr);
  if ((carrier == 0.0 && strcmp (subtoken, endptr) == 0) 
      || (*endptr != '\0')
      || errno != 0)
    error ("Carrier for chronaural had an error.\n%s\n%s", subtoken, original);
  else if (carrier <= 0.0)  // no errors, but less than equal to zero
    error ("Carrier for chronaural cannot be less than or equal to 0.\n%s\n%s", subtoken, original);
  if (opt_m) // modify carrier and beat read from script file
  {
    double band = carrier * modify;  // amount of possible variance
    double adjust = (drand48 ()) * band;  // adjustment amount
    adjust -= (band / 2.);
    carrier += adjust;
  }
  chronaural1->carrier = carrier;

  subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
  errno = 0;
  double beat = strtod (subtoken, &endptr);
  if ((beat == 0.0 && strcmp (subtoken, endptr) == 0)
      || (*endptr != '\0')
      || errno != 0)
    error ("Beat for chronaural had an error.\n%s\n%s", subtoken, original);
  if (opt_m) // modify carrier and beat read from script file
  {
    double band = (fabs (beat)) * modify;  // amount of possible variance
    double adjust = (drand48 ()) * band;  // adjustment amount
    adjust -= (band / 2.);
    beat += adjust;
  }
  chronaural1->beat = beat;

  subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
  errno = 0;
  double amp = strtod (subtoken, &endptr);
  if ((amp == 0.0 && strcmp (subtoken, endptr) == 0)
      || (*endptr != '\0')
      || errno != 0)
    error ("Amplitude for chronaural had an error.\n%s\n%s", subtoken, original);
  else if (amp < 0.0)  // no errors, but less than zero
    error ("Amplitude for chronaural cannot be less than 0.\n%s\n%s", subtoken, original);
  chronaural1->amp = AMP_AD(amp);

  subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
  errno = 0;
  double phase = strtod (subtoken, &endptr);
  if ((phase == 0.0 && strcmp (subtoken, endptr) == 0)
      || (*endptr != '\0')
      || errno != 0)
    error ("Phase for chronaural had an error.\n%s\n%s", subtoken, original);
  else if (phase < 0.0 || phase > 360.0)  // no errors, but less than zero or greater than 360
    error ("Phase for chronaural cannot be less than 0 or greater than 360.\n%s\n%s", subtoken, original);
  chronaural1->phase = phase;

  subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
  errno = 0;
  double sin_threshold = strtod (subtoken, &endptr);
  if ((sin_threshold == 0.0 && strcmp (subtoken, endptr) == 0)
      || (*endptr != '\0')
      || errno != 0)
    error ("Sin threshold for chronaural had an error.\n%s\n%s", subtoken, original);
  else if (sin_threshold < 0.0 || sin_threshold >= 1.0)  // no errors, but less than zero or greater than 1
    error ("Sin threshold for chronaural cannot be less than 0 or greater than 1.\n%s\n%s", subtoken, original);
  chronaural1->sin_threshold = sin_threshold;

  subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
  errno = 0;
  double beat_behave = strtod (subtoken, &endptr);
  if ((beat_behave == 0.0 && strcmp (subtoken, endptr) == 0)
      || (*endptr != '\0')
      || errno != 0)
    error ("Beat behavior for chronaural had an error.\n%s\n%s", subtoken, original);
  else if (beat_behave < 1.0 || beat_behave > 4.0)  // no errors, but outside behavior range
    error ("Beat behavior for chronaural cannot be less than 1 or greater than 4.\n%s\n%s", subtoken, original);
  chronaural1->beat_behave = beat_behave;

  subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
  errno = 0;
  double split_begin = strtod (subtoken, &endptr);
  if ((split_begin == 0.0 && strcmp (subtoken, endptr) == 0)
      || (*endptr != '\0')
      || errno != 0)
    error ("Beginning split for chronaural had an error.\n%s\n%s", subtoken, original);
  else if ((split_begin < 0.0 && split_begin != -1.0) || split_begin > 1.0)  // no errors, but less than zero, greater than 1
    error ("Beginning split for chronaural cannot be less than 0 except for -1, or greater than 1.\n%s\n%s", 
                                                                   subtoken, original);
  chronaural1->split_begin = split_begin;

  subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
  errno = 0;
  double split_end = strtod (subtoken, &endptr);
  if ((split_end == 0.0 && strcmp (subtoken, endptr) == 0)
      || (*endptr != '\0')
      || errno != 0)
    error ("Ending split for chronaural had an error.\n%s\n%s", subtoken, original);
  else if ((split_end < 0.0 && split_end != -1.0) || split_end > 1.0)  // no errors, but less than zero, greater than 1
    error ("Ending split for chronaural cannot be less than 0 except for -1, or greater than 1.\n%s\n%s", subtoken, original);
  chronaural1->split_end = split_end;

  subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
  errno = 0;
  double split_low = strtod (subtoken, &endptr);
  if ((split_low == 0.0 && strcmp (subtoken, endptr) == 0)
      || (*endptr != '\0')
      || errno != 0)
    error ("Low split limit for chronaural had an error.\n%s\n%s", subtoken, original);
  else if (split_low < 0.0 || split_low > 1.0)  // no errors, but less than zero, greater than 1
    error ("Low split limit for chronaural cannot be less than 0 or greater than 1.\n%s\n%s", subtoken, original);
  chronaural1->split_low = split_low;

  subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
  errno = 0;
  double split_high = strtod (subtoken, &endptr);
  if ((split_high == 0.0 && strcmp (subtoken, endptr) == 0)
      || (*endptr != '\0')
      || errno != 0)
    error ("High split limit for chronaural had an error.\n%s\n%s", subtoken, original);
  else if (split_high < split_low || split_high > 1.0)  // no errors, but less than split_low or greater than 1
    error ("High split limit for chronaural cannot be less than low split limit or greater than 1.\n%s\n%s", 
                                                                    subtoken, original);
  chronaural1->split_high = split_high;

  subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
  errno = 0;
  double split_beat = strtod (subtoken, &endptr);
  if ((split_beat == 0.0 && strcmp (subtoken, endptr) == 0)
      || (*endptr != '\0')
      || errno != 0)
    error ("Split beat for chronaural had an error.\n%s\n%s", subtoken, original);
  else if (split_beat < 0.0)  // no errors, but less than 0
    error ("Split beat for chronaural cannot be less than 0.\n%s\n%s", subtoken, original);
  chronaural1->split_beat = split_beat;

  subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
  errno = 0;
  if (subtoken != NULL && strcmp (subtoken, ">") == 0)
    chronaural1->slide = 1;
  else if (subtoken != NULL && strcmp (subtoken, "&") == 0)  // it's there a step slide, no amp variation
  {
    chronaural1->type = 10;  // chronaural step slide
    chronaural1->slide = 2;  // chronaural step slide

    subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
    errno = 0;
    double steps = strtod (subtoken, &endptr);
    if ((steps == 0.0 && strcmp (subtoken, endptr) == 0)
        || (*endptr != '\0')
        || errno != 0)
      error ("Step count for chronaural had an error.\n%s\n%s", subtoken, original);
    else if (steps <= 0.0)  // no errors, but less than equal to zero
      error ("Step count for chronaural cannot be less than or equal to 0.\n%s\n%s", subtoken, original);
    chronaural1->steps = (int) steps;

    subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
    errno = 0;
    double slide_time = strtod (subtoken, &endptr);
    if ((slide_time == 0.0 && strcmp (subtoken, endptr) == 0)
        || (*endptr != '\0')
        || errno != 0)
      error ("Slide time for chronaural had an error.\n%s\n%s", subtoken, original);
    else if (slide_time <= 0.0)  // no errors, but less than equal to zero
      error ("Slide time for chronaural cannot be less than or equal to 0.\n%s\n%s", subtoken, original);
    chronaural1->slide_time = slide_time;

    subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
    errno = 0;
    double fuzz = strtod (subtoken, &endptr);
    if ((fuzz == 0.0 && strcmp (subtoken, endptr) == 0)
        || (*endptr != '\0')
        || errno != 0)
      error ("Fuzz for chronaural had an error.\n%s\n%s", subtoken, original);
    else if (fuzz < 0.0)  // no errors, but less than zero
      error ("Fuzz for chronaural cannot be less than 0.\n%s\n%s", subtoken, original);
    chronaural1->fuzz = AMP_AD(fuzz);
  }
  else if (subtoken != NULL && strcmp (subtoken, "~") == 0)  // it's there a vary, no amp variation
  {
    chronaural1->type = 12;  // chronaural vary slide
    chronaural1->slide = 3;  // chronaural vary slide

    subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
    errno = 0;
    double steps = strtod (subtoken, &endptr);
    if ((steps == 0.0 && strcmp (subtoken, endptr) == 0)
        || (*endptr != '\0')
        || errno != 0)
      error ("Step count for chronaural had an error.\n%s\n%s", subtoken, original);
    else if (steps <= 0.0)  // no errors, but less than equal to zero
      error ("Step count for chronaural cannot be less than or equal to 0.\n%s\n%s", subtoken, original);
    chronaural1->steps = (int) steps;

    subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
    errno = 0;
    double slide_time = strtod (subtoken, &endptr);
    if ((slide_time == 0.0 && strcmp (subtoken, endptr) == 0)
        || (*endptr != '\0')
        || errno != 0)
      error ("Slide time for chronaural had an error.\n%s\n%s", subtoken, original);
    else if (slide_time <= 0.0)  // no errors, but less than equal to zero
      error ("Slide time for chronaural cannot be less than or equal to 0.\n%s\n%s", subtoken, original);
    chronaural1->slide_time = slide_time;
  }
  else if (subtoken != NULL) // invalid slide indicator
    error ("Slide indicator for chronaural had an error.\n%s\n%s", subtoken, original);
}

/* Set up a pulse sequence */

void
setup_pulse (char *token, void **work)
{
  char *original;
  char *endptr;
  char *subtoken;
  char *str2 = NULL;
  char *saveptr2;
  pulse *pulse1 = NULL;

  pulse1 = (pulse *) Alloc ((sizeof (pulse)) * 1);
  *work = (void *) pulse1;
  pulse1->next = NULL;
  pulse1->type = 13;
  pulse1->slide = 0;  // default to not slide
  pulse1->off1 = pulse1->off3 = pulse1->off2 = 0;  // begin at 0 degrees
  pulse1->last_off1 = pulse1->last_off3 = pulse1->last_off2 = NULL;  // no previous voice offsets yet
  pulse1->first_pass = 1;  // inactive
  /* used for step and vary */
  pulse1->step_next = NULL;  // default no steps
  pulse1->tot_frames = 0;  // total frames for this step
  pulse1->cur_frames = 0;  // current frames for this step
  pulse1->steps = 0;  // no steps
  pulse1->slide_time = 0.0;  // no slide between steps
  pulse1->fuzz = 0.0;  // no fuzziness around step frequency
  original = StrDup (token);
  str2 = token;

  subtoken = strtok_r (str2, separators, &saveptr2);        // remove voice type
  str2 = NULL;
  
  subtoken = strtok_r (str2, separators, &saveptr2);        // get subtoken of token
  errno = 0;
  double carrier = strtod (subtoken, &endptr);
  if ((carrier == 0.0 && strcmp (subtoken, endptr) == 0) 
      || (*endptr != '\0')
      || errno != 0)
    error ("Carrier for pulse had an error.\n%s\n%s", subtoken, original);
  else if (carrier <= 0.0)  // no errors, but less than equal to zero
    error ("Carrier for pulse cannot be less than or equal to 0.\n%s\n%s", subtoken, original);
  if (opt_m) // modify carrier and beat read from script file
  {
    double band = carrier * modify;  // amount of possible variance
    double adjust = (drand48 ()) * band;  // adjustment amount
    adjust -= (band / 2.);
    carrier += adjust;
  }
  pulse1->carrier = carrier;

  subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
  errno = 0;
  double beat = strtod (subtoken, &endptr);
  if ((beat == 0.0 && strcmp (subtoken, endptr) == 0)
      || (*endptr != '\0')
      || errno != 0)
    error ("Beat for pulse had an error.\n%s\n%s", subtoken, original);
  if (opt_m) // modify carrier and beat read from script file
  {
    double band = (fabs (beat)) * modify;  // amount of possible variance
    double adjust = (drand48 ()) * band;  // adjustment amount
    adjust -= (band / 2.);
    beat += adjust;
  }
  pulse1->beat = beat;

  subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
  errno = 0;
  double amp = strtod (subtoken, &endptr);
  if ((amp == 0.0 && strcmp (subtoken, endptr) == 0)
      || (*endptr != '\0')
      || errno != 0)
    error ("Amplitude for pulse had an error.\n%s\n%s", subtoken, original);
  else if (amp < 0.0)  // no errors, but less than zero
    error ("Amplitude for pulse cannot be less than 0.\n%s\n%s", subtoken, original);
  pulse1->amp = AMP_AD(amp);

  subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
  errno = 0;
  double phase = strtod (subtoken, &endptr);
  if ((phase == 0.0 && strcmp (subtoken, endptr) == 0)
      || (*endptr != '\0')
      || errno != 0)
    error ("Phase for pulse had an error.\n%s\n%s", subtoken, original);
  else if (phase < 0.0 || phase > 360.0)  // no errors, but less than zero or greater than 360
    error ("Phase for pulse cannot be less than 0 or greater than 360.\n%s\n%s", subtoken, original);
  pulse1->phase = phase;

  subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
  errno = 0;
  double time = strtod (subtoken, &endptr);
  if ((time == 0.0 && strcmp (subtoken, endptr) == 0)
      || (*endptr != '\0')
      || errno != 0)
    error ("Pulse time for pulse had an error.\n%s\n%s", subtoken, original);
  else if (time < 0.0)  // no errors, but less than zero
    error ("Pulse time for pulse cannot be less than 0.\n%s\n%s", subtoken, original);
  pulse1->time = time;

  subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
  errno = 0;
  double split_begin = strtod (subtoken, &endptr);
  if ((split_begin == 0.0 && strcmp (subtoken, endptr) == 0)
      || (*endptr != '\0')
      || errno != 0)
    error ("Beginning split for pulse had an error.\n%s\n%s", subtoken, original);
  else if ((split_begin < 0.0 && split_begin != -1.0) || split_begin > 1.0)  // no errors, but less than zero, greater than 1
    error ("Beginning split for pulse cannot be less than 0 except for -1, or greater than 1.\n%s\n%s", subtoken, original);
  pulse1->split_begin = split_begin;

  subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
  errno = 0;
  double split_end = strtod (subtoken, &endptr);
  if ((split_end == 0.0 && strcmp (subtoken, endptr) == 0)
      || (*endptr != '\0')
      || errno != 0)
    error ("Ending split for pulse had an error.\n%s\n%s", subtoken, original);
  else if ((split_end < 0.0 && split_end != -1.0) || split_end > 1.0)  // no errors, but less than zero, greater than 1
    error ("Ending split for pulse cannot be less than 0 except for -1, or greater than 1.\n%s\n%s", subtoken, original);
  pulse1->split_end = split_end;

  subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
  errno = 0;
  double split_low = strtod (subtoken, &endptr);
  if ((split_low == 0.0 && strcmp (subtoken, endptr) == 0)
      || (*endptr != '\0')
      || errno != 0)
    error ("Low split limit for pulse had an error.\n%s\n%s", subtoken, original);
  else if (split_low < 0.0 || split_low > 1.0)  // no errors, but less than zero, greater than 1
    error ("Low split limit for pulse cannot be less than 0 or greater than 1.\n%s\n%s", subtoken, original);
  pulse1->split_low = split_low;

  subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
  errno = 0;
  double split_high = strtod (subtoken, &endptr);
  if ((split_high == 0.0 && strcmp (subtoken, endptr) == 0)
      || (*endptr != '\0')
      || errno != 0)
    error ("High split limit for pulse had an error.\n%s\n%s", subtoken, original);
  else if (split_high < split_low || split_high > 1.0)  // no errors, but less than split_low or greater than 1
    error ("High split limit for pulse cannot be less than low split limit or greater than 1.\n%s\n%s", subtoken, original);
  pulse1->split_high = split_high;

  subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
  errno = 0;
  double split_beat = strtod (subtoken, &endptr);
  if ((split_beat == 0.0 && strcmp (subtoken, endptr) == 0)
      || (*endptr != '\0')
      || errno != 0)
    error ("Split beat for pulse had an error.\n%s\n%s", subtoken, original);
  else if (split_beat < 0.0)  // no errors, but less than 0
    error ("Split beat for pulse cannot be less than 0.\n%s\n%s", subtoken, original);
  pulse1->split_beat = split_beat;

  subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
  errno = 0;
  if (subtoken != NULL && strcmp (subtoken, ">") == 0)  // regular slide
    pulse1->slide = 1;
  else if (subtoken != NULL && strcmp (subtoken, "&") == 0)  // a step slide
  {
    pulse1->type = 14;  // pulse step slide
    pulse1->slide = 2;  // pulse step slide

    subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
    errno = 0;
    double steps = strtod (subtoken, &endptr);
    if ((steps == 0.0 && strcmp (subtoken, endptr) == 0)
        || (*endptr != '\0')
        || errno != 0)
      error ("Step count for pulse had an error.\n%s\n%s", subtoken, original);
    else if (steps <= 0.0)  // no errors, but less than equal to zero
      error ("Step count for pulse cannot be less than or equal to 0.\n%s\n%s", subtoken, original);
    pulse1->steps = (int) steps;

    subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
    errno = 0;
    double slide_time = strtod (subtoken, &endptr);
    if ((slide_time == 0.0 && strcmp (subtoken, endptr) == 0)
        || (*endptr != '\0')
        || errno != 0)
      error ("Slide time for pulse had an error.\n%s\n%s", subtoken, original);
    else if (slide_time <= 0.0)  // no errors, but less than equal to zero
      error ("Slide time for pulse cannot be less than or equal to 0.\n%s\n%s", subtoken, original);
    pulse1->slide_time = slide_time;

    subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
    errno = 0;
    double fuzz = strtod (subtoken, &endptr);
    if ((fuzz == 0.0 && strcmp (subtoken, endptr) == 0)
        || (*endptr != '\0')
        || errno != 0)
      error ("Fuzz for pulse had an error.\n%s\n%s", subtoken, original);
    else if (fuzz < 0.0)  // no errors, but less than zero
      error ("Fuzz for pulse cannot be less than 0.\n%s\n%s", subtoken, original);
    pulse1->fuzz = AMP_AD(fuzz);
  }
  else if (subtoken != NULL && strcmp (subtoken, "~") == 0)  // a vary slide
  {
    pulse1->type = 15;  // pulse vary slide
    pulse1->slide = 3;  // pulse vary slide

    subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
    errno = 0;
    double steps = strtod (subtoken, &endptr);
    if ((steps == 0.0 && strcmp (subtoken, endptr) == 0)
        || (*endptr != '\0')
        || errno != 0)
      error ("Step count for pulse had an error.\n%s\n%s", subtoken, original);
    else if (steps <= 0.0)  // no errors, but less than equal to zero
      error ("Step count for pulse cannot be less than or equal to 0.\n%s\n%s", subtoken, original);
    pulse1->steps = (int) steps;

    subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
    errno = 0;
    double slide_time = strtod (subtoken, &endptr);
    if ((slide_time == 0.0 && strcmp (subtoken, endptr) == 0)
        || (*endptr != '\0')
        || errno != 0)
      error ("Slide time for pulse had an error.\n%s\n%s", subtoken, original);
    else if (slide_time <= 0.0)  // no errors, but less than equal to zero
      error ("Slide time for pulse cannot be less than or equal to 0.\n%s\n%s", subtoken, original);
    pulse1->slide_time = slide_time;
  }
  else if (subtoken != NULL) // invalid slide indicator
    error ("Slide indicator for pulse had an error.\n%s\n%s", subtoken, original);
}

/* Set up a phase sequence */

void
setup_phase (char *token, void **work)
{
  char *original;
  char *endptr;
  char *subtoken;
  char *str2 = NULL;
  char *saveptr2;
  phase *phase1 = NULL;

  phase1 = (phase *) Alloc ((sizeof (phase)) * 1);
  *work = (void *) phase1;
  phase1->next = NULL;
  phase1->type = 16;
  phase1->slide = 0;  // default to not slide
  phase1->off1 = 0;  // begin at 0 degrees
  phase1->shift = 0;  // begin at 0 shift
  phase1->direction = 1;  // begin with shift towards maximum phase
  phase1->last_off1 = NULL;  // no previous voice offsets yet
  phase1->last_shift = phase1->last_direction = NULL;  // no previous shift or direction offsets yet
  phase1->last_amp_off1 = phase1->last_amp_off2 = NULL;  // no previous voice offsets yet
  phase1->first_pass = 1;  // inactive
  /* used for step and vary */
  phase1->step_next = NULL;  // default no steps
  phase1->tot_frames = 0;  // total frames for this step
  phase1->cur_frames = 0;  // current frames for this step
  phase1->steps = 0;  // no steps
  phase1->slide_time = 0.0;  // no slide between steps
  phase1->fuzz = 0.0;  // no fuzziness around step frequency
  original = StrDup (token);
  str2 = token;

  subtoken = strtok_r (str2, separators, &saveptr2);        // remove voice type
  str2 = NULL;
  
  subtoken = strtok_r (str2, separators, &saveptr2);        // get subtoken of token
  errno = 0;
  double carrier = strtod (subtoken, &endptr);
  if ((carrier == 0.0 && strcmp (subtoken, endptr) == 0) 
      || (*endptr != '\0')
      || errno != 0)
    error ("Carrier for phase had an error.\n%s\n%s", subtoken, original);
  else if (carrier <= 0.0)  // no errors, but less than equal to zero
    error ("Carrier for phase cannot be less than or equal to 0.\n%s\n%s", subtoken, original);
  if (opt_m) // modify carrier and beat read from script file
  {
    double band = carrier * modify;  // amount of possible variance
    double adjust = (drand48 ()) * band;  // adjustment amount
    adjust -= (band / 2.);
    carrier += adjust;
  }
  phase1->carrier = carrier;

  subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
  errno = 0;
  double beat = strtod (subtoken, &endptr);
  if ((beat == 0.0 && strcmp (subtoken, endptr) == 0)
      || (*endptr != '\0')
      || errno != 0)
    error ("Beat for phase had an error.\n%s\n%s", subtoken, original);
  if (opt_m) // modify carrier and beat read from script file
  {
    double band = (fabs (beat)) * modify;  // amount of possible variance
    double adjust = (drand48 ()) * band;  // adjustment amount
    adjust -= (band / 2.);
    beat += adjust;
  }
  phase1->beat = beat;

  subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
  errno = 0;
  double amp = strtod (subtoken, &endptr);
  if ((amp == 0.0 && strcmp (subtoken, endptr) == 0)
      || (*endptr != '\0')
      || errno != 0)
    error ("Amplitude for phase had an error.\n%s\n%s", subtoken, original);
  else if (amp < 0.0)  // no errors, but less than zero
    error ("Amplitude for phase cannot be less than 0.\n%s\n%s", subtoken, original);
  phase1->amp = AMP_AD(amp);

  subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
  errno = 0;
  double phase = strtod (subtoken, &endptr);
  if ((phase == 0.0 && strcmp (subtoken, endptr) == 0)
      || (*endptr != '\0')
      || errno != 0)
    error ("Phase for phase had an error.\n%s\n%s", subtoken, original);
  else if (phase < 0.0 || phase > 360.0)  // no errors, but less than zero or greater than 360
    error ("Phase for phase cannot be less than 0 or greater than 360.\n%s\n%s", subtoken, original);
  phase1->phase = phase;

  subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
  if (subtoken != NULL && strcmp (subtoken, ">") == 0)  // it's there and slide, done, no amp variation
    phase1->slide = 1;
  else if (subtoken != NULL && strcmp (subtoken, "&") == 0)  // it's there and step slide, no amp variation
  {
    phase1->type = 17;  // phase step
    phase1->slide = 2;  // phase step slide

    subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
    errno = 0;
    double steps = strtod (subtoken, &endptr);
    if ((steps == 0.0 && strcmp (subtoken, endptr) == 0)
        || (*endptr != '\0')
        || errno != 0)
      error ("Step count for phase had an error.\n%s\n%s", subtoken, original);
    else if (steps <= 0.0)  // no errors, but less than equal to zero
      error ("Step count for phase cannot be less than or equal to 0.\n%s\n%s", subtoken, original);
    phase1->steps = (int) steps;

    subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
    errno = 0;
    double slide_time = strtod (subtoken, &endptr);
    if ((slide_time == 0.0 && strcmp (subtoken, endptr) == 0)
        || (*endptr != '\0')
        || errno != 0)
      error ("Slide time for phase had an error.\n%s\n%s", subtoken, original);
    else if (slide_time <= 0.0)  // no errors, but less than equal to zero
      error ("Slide time for phase cannot be less than or equal to 0.\n%s\n%s", subtoken, original);
    phase1->slide_time = slide_time;

    subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
    errno = 0;
    double fuzz = strtod (subtoken, &endptr);
    if ((fuzz == 0.0 && strcmp (subtoken, endptr) == 0)
        || (*endptr != '\0')
        || errno != 0)
      error ("Fuzz for phase had an error.\n%s\n%s", subtoken, original);
    else if (fuzz < 0.0)  // no errors, but less than zero
      error ("Fuzz for phase cannot be less than 0.\n%s\n%s", subtoken, original);
    phase1->fuzz = AMP_AD(fuzz);
  }
  else if (subtoken != NULL && strcmp (subtoken, "~") == 0)  // it's there and vary, no amp variation
  {
    phase1->type = 18;  // phase vary
    phase1->slide = 3;  // phase vary slide

    subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
    errno = 0;
    double steps = strtod (subtoken, &endptr);
    if ((steps == 0.0 && strcmp (subtoken, endptr) == 0)
        || (*endptr != '\0')
        || errno != 0)
      error ("Step count for phase had an error.\n%s\n%s", subtoken, original);
    else if (steps <= 0.0)  // no errors, but less than equal to zero
      error ("Step count for phase cannot be less than or equal to 0.\n%s\n%s", subtoken, original);
    phase1->steps = (int) steps;

    subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
    errno = 0;
    double slide_time = strtod (subtoken, &endptr);
    if ((slide_time == 0.0 && strcmp (subtoken, endptr) == 0)
        || (*endptr != '\0')
        || errno != 0)
      error ("Slide time for phase had an error.\n%s\n%s", subtoken, original);
    else if (slide_time <= 0.0)  // no errors, but less than equal to zero
      error ("Slide time for phase cannot be less than or equal to 0.\n%s\n%s", subtoken, original);
    phase1->slide_time = slide_time;
  }
  else if (subtoken != NULL)  // it's there, not slide, step, or vary, must be amp variation
  {
    errno = 0;
    double amp_beat1 = strtod (subtoken, &endptr);
    if ((amp_beat1 == 0.0 && strcmp (subtoken, endptr) == 0)
        || (*endptr != '\0')
        || errno != 0)
      error ("Amplitude beat1 for phase had an error.\n%s\n%s", subtoken, original);
    else if (amp_beat1 < 0.0)  // no errors, but less than zero
      error ("Amplitude beat1 for phase cannot be less than 0.\n%s\n%s", subtoken, original);
    phase1->amp_beat1 = amp_beat1;

    subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
    errno = 0;
    double amp_beat2 = strtod (subtoken, &endptr);
    if ((amp_beat2 == 0.0 && strcmp (subtoken, endptr) == 0)
        || (*endptr != '\0')
        || errno != 0)
      error ("Amplitude beat2 for phase had an error.\n%s\n%s", subtoken, original);
    else if (amp_beat2 < 0.0)  // no errors, but less than zero
      error ("Amplitude beat2 for phase cannot be less than 0.\n%s\n%s", subtoken, original);
    phase1->amp_beat2 = amp_beat2;

    subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
    errno = 0;
    double amp_pct1 = strtod (subtoken, &endptr);
    if ((amp_pct1 == 0.0 && strcmp (subtoken, endptr) == 0)
        || (*endptr != '\0')
        || errno != 0)
      error ("Amplitude adj1 for phase had an error.\n%s\n%s", subtoken, original);
    else if (amp_pct1 < 0.0)  // no errors, but less than zero
      error ("Amplitude adj1 for phase cannot be less than 0.\n%s\n%s", subtoken, original);
    phase1->amp_pct1 = AMP_AD(amp_pct1);

    subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
    errno = 0;
    double amp_pct2 = strtod (subtoken, &endptr);
    if ((amp_pct2 == 0.0 && strcmp (subtoken, endptr) == 0)
        || (*endptr != '\0')
        || errno != 0)
      error ("Amplitude adj2 for phase had an error.\n%s\n%s", subtoken, original);
    else if (amp_pct2 < 0.0)  // no errors, but less than zero
      error ("Amplitude adj2 for phase cannot be less than 0.\n%s\n%s", subtoken, original);
    phase1->amp_pct2 = AMP_AD(amp_pct2);

    subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
    if (subtoken != NULL && strcmp (subtoken, ">") == 0)  // slide
      phase1->slide = 1;
    else if (subtoken != NULL && strcmp (subtoken, "&") == 0)  // step slide
    {
      phase1->type = 17;  // phase step
      phase1->slide = 2;  // phase step slide

      subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
      errno = 0;
      double steps = strtod (subtoken, &endptr);
      if ((steps == 0.0 && strcmp (subtoken, endptr) == 0)
          || (*endptr != '\0')
          || errno != 0)
        error ("Step count for phase had an error.\n%s\n%s", subtoken, original);
      else if (steps <= 0.0)  // no errors, but less than equal to zero
        error ("Step count for phase cannot be less than or equal to 0.\n%s\n%s", subtoken, original);
      phase1->steps = (int) steps;

      subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
      errno = 0;
      double slide_time = strtod (subtoken, &endptr);
      if ((slide_time == 0.0 && strcmp (subtoken, endptr) == 0)
          || (*endptr != '\0')
          || errno != 0)
        error ("Slide time for phase had an error.\n%s\n%s", subtoken, original);
      else if (slide_time <= 0.0)  // no errors, but less than equal to zero
        error ("Slide time for phase cannot be less than or equal to 0.\n%s\n%s", subtoken, original);
      phase1->slide_time = slide_time;

      subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
      errno = 0;
      double fuzz = strtod (subtoken, &endptr);
      if ((fuzz == 0.0 && strcmp (subtoken, endptr) == 0)
          || (*endptr != '\0')
          || errno != 0)
        error ("Fuzz for phase had an error.\n%s\n%s", subtoken, original);
      else if (fuzz < 0.0)  // no errors, but less than zero
        error ("Fuzz for phase cannot be less than 0.\n%s\n%s", subtoken, original);
      phase1->fuzz = AMP_AD(fuzz);
    }
    else if (subtoken != NULL && strcmp (subtoken, "~") == 0)  // vary
    {
      phase1->type = 18;  // phase vary
      phase1->slide = 3;  // phase vary slide

      subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
      errno = 0;
      double steps = strtod (subtoken, &endptr);
      if ((steps == 0.0 && strcmp (subtoken, endptr) == 0)
          || (*endptr != '\0')
          || errno != 0)
        error ("Step count for phase had an error.\n%s\n%s", subtoken, original);
      else if (steps <= 0.0)  // no errors, but less than equal to zero
        error ("Step count for phase cannot be less than or equal to 0.\n%s\n%s", subtoken, original);
      phase1->steps = (int) steps;

      subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
      errno = 0;
      double slide_time = strtod (subtoken, &endptr);
      if ((slide_time == 0.0 && strcmp (subtoken, endptr) == 0)
          || (*endptr != '\0')
          || errno != 0)
        error ("Slide time for phase had an error.\n%s\n%s", subtoken, original);
      else if (slide_time <= 0.0)  // no errors, but less than equal to zero
        error ("Slide time for phase cannot be less than or equal to 0.\n%s\n%s", subtoken, original);
      phase1->slide_time = slide_time;
    }
    else if (subtoken != NULL) // invalid slide indicator
      error ("Slide indicator for binaural had an error.\n%s\n%s", subtoken, original);
  }
}

/* Set up an fm sequence */

void
setup_fm (char *token, void **work)
{
  char *original;
  char *endptr;
  char *subtoken;
  char *str2 = NULL;
  char *saveptr2;
  fm *fm1 = NULL;

  fm1 = (fm *) Alloc ((sizeof (fm)) * 1);
  *work = (void *) fm1;
  fm1->next = NULL;
  fm1->type = 19;
  fm1->slide = 0;  // default to not slide
  fm1->off1 = 0;  // begin at 0 degrees
  fm1->shift = 0.0;  // begin at 0 shift
  fm1->direction = 1;  // begin with shift towards maximum freq
  fm1->last_off1 = NULL;  // no previous voice offsets yet
  fm1->last_shift = NULL;  // no previous shift yet
  fm1->last_direction = NULL;  // no previous direction yet
  fm1->last_amp_off1 = fm1->last_amp_off2 = NULL;  // no previous voice offsets yet
  fm1->first_pass = 1;  // inactive
  /* used for step and vary */
  fm1->step_next = NULL;  // default no steps
  fm1->tot_frames = 0;  // total frames for this step
  fm1->cur_frames = 0;  // current frames for this step
  fm1->steps = 0;  // no steps
  fm1->slide_time = 0.0;  // no slide between steps
  fm1->fuzz = 0.0;  // no fuzziness around step frequency
  original = StrDup (token);
  str2 = token;

  subtoken = strtok_r (str2, separators, &saveptr2);        // remove voice type
  str2 = NULL;
  
  subtoken = strtok_r (str2, separators, &saveptr2);        // get subtoken of token
  errno = 0;
  double carrier = strtod (subtoken, &endptr);
  if ((carrier == 0.0 && strcmp (subtoken, endptr) == 0) 
      || (*endptr != '\0')
      || errno != 0)
    error ("Carrier for fm had an error.\n%s\n%s", subtoken, original);
  else if (carrier <= 0.0)  // no errors, but less than equal to zero
    error ("Carrier for fm cannot be less than or equal to 0.\n%s\n%s", subtoken, original);
  if (opt_m) // modify carrier and beat read from script file
  {
    double band = carrier * modify;  // amount of possible variance
    double adjust = (drand48 ()) * band;  // adjustment amount
    adjust -= (band / 2.);
    carrier += adjust;
  }
  fm1->carrier = carrier;

  subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
  errno = 0;
  double beat = strtod (subtoken, &endptr);
  if ((beat == 0.0 && strcmp (subtoken, endptr) == 0)
      || (*endptr != '\0')
      || errno != 0)
    error ("Beat for fm had an error.\n%s\n%s", subtoken, original);
  else if (beat < 0.0)  // no errors, but less than zero
    error ("Beat for fm cannot be less than 0.\n%s\n%s", subtoken, original);
  if (opt_m) // modify carrier and beat read from script file
  {
    double band = beat * modify;  // amount of possible variance
    double adjust = (drand48 ()) * band;  // adjustment amount
    adjust -= (band / 2.);
    beat += adjust;
  }
  fm1->beat = beat;
  
  subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
  errno = 0;
  double amp = strtod (subtoken, &endptr);
  if ((amp == 0.0 && strcmp (subtoken, endptr) == 0)
      || (*endptr != '\0')
      || errno != 0)
    error ("Amplitude for fm had an error.\n%s\n%s", subtoken, original);
  else if (amp < 0.0)  // no errors, but less than zero
    error ("Amplitude for fm cannot be less than 0.\n%s\n%s", subtoken, original);
  fm1->amp = AMP_AD(amp);

  subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
  errno = 0;
  double band = strtod (subtoken, &endptr);
  if ((band == 0.0 && strcmp (subtoken, endptr) == 0)
      || (*endptr != '\0')
      || errno != 0)
    error ("Band for fm had an error.\n%s\n%s", subtoken, original);
  else if (band < 0.0)  // no errors, but less than zero
    error ("Band for fm cannot be less than 0.\n%s\n%s", subtoken, original);
  fm1->band = band;

  subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
  if (subtoken != NULL && strcmp (subtoken, "L") == 0)  // left channel only
    fm1->channel = 1;
  else if (subtoken != NULL && strcmp (subtoken, "R") == 0)  // right channel only
    fm1->channel = 2;
  else if (subtoken != NULL && strcmp (subtoken, "B") == 0)  // both channels
    fm1->channel = 3;
  else  // unrecognized, print error message
    error ("Channel for freq had an error.  Only L, R, B allowed.\n%s\n%s", subtoken, original);

  subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
  errno = 0;
  double phase = strtod (subtoken, &endptr);
  if ((phase == 0.0 && strcmp (subtoken, endptr) == 0)
      || (*endptr != '\0')
      || errno != 0)
    error ("Phase for fm had an error.\n%s\n%s", subtoken, original);
  else if (phase < -360.0 || phase > 360.0)  // no errors, but less than zero or greater than 360
    error ("Phase for fm cannot be less than -360 or greater than 360.\n%s\n%s", subtoken, original);
  fm1->phase = phase;

  subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
  if (subtoken != NULL && strcmp (subtoken, ">") == 0)  // it's there and slide, done, no amp variation
    fm1->slide = 1;
  else if (subtoken != NULL && strcmp (subtoken, "&") == 0)  // it's there and step slide, no amp variation
  {
    fm1->type = 20;  // freq step
    fm1->slide = 2;  // freq step slide

    subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
    errno = 0;
    double steps = strtod (subtoken, &endptr);
    if ((steps == 0.0 && strcmp (subtoken, endptr) == 0)
        || (*endptr != '\0')
        || errno != 0)
      error ("Step count for fm had an error.\n%s\n%s", subtoken, original);
    else if (steps <= 0.0)  // no errors, but less than equal to zero
      error ("Step count for fm cannot be less than or equal to 0.\n%s\n%s", subtoken, original);
    fm1->steps = (int) steps;

    subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
    errno = 0;
    double slide_time = strtod (subtoken, &endptr);
    if ((slide_time == 0.0 && strcmp (subtoken, endptr) == 0)
        || (*endptr != '\0')
        || errno != 0)
      error ("Slide time for fm had an error.\n%s\n%s", subtoken, original);
    else if (slide_time <= 0.0)  // no errors, but less than equal to zero
      error ("Slide time for fm cannot be less than or equal to 0.\n%s\n%s", subtoken, original);
    fm1->slide_time = slide_time;

    subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
    errno = 0;
    double fuzz = strtod (subtoken, &endptr);
    if ((fuzz == 0.0 && strcmp (subtoken, endptr) == 0)
        || (*endptr != '\0')
        || errno != 0)
      error ("Fuzz for fm had an error.\n%s\n%s", subtoken, original);
    else if (fuzz < 0.0)  // no errors, but less than zero
      error ("Fuzz for fm cannot be less than 0.\n%s\n%s", subtoken, original);
    fm1->fuzz = AMP_AD(fuzz);
  }
  else if (subtoken != NULL && strcmp (subtoken, "~") == 0)  // it's there and vary, no amp variation
  {
    fm1->type = 21;  // freq vary
    fm1->slide = 3;  // freq vary slide

    subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
    errno = 0;
    double steps = strtod (subtoken, &endptr);
    if ((steps == 0.0 && strcmp (subtoken, endptr) == 0)
        || (*endptr != '\0')
        || errno != 0)
      error ("Step count for fm had an error.\n%s\n%s", subtoken, original);
    else if (steps <= 0.0)  // no errors, but less than equal to zero
      error ("Step count for fm cannot be less than or equal to 0.\n%s\n%s", subtoken, original);
    fm1->steps = (int) steps;

    subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
    errno = 0;
    double slide_time = strtod (subtoken, &endptr);
    if ((slide_time == 0.0 && strcmp (subtoken, endptr) == 0)
        || (*endptr != '\0')
        || errno != 0)
      error ("Slide time for fm had an error.\n%s\n%s", subtoken, original);
    else if (slide_time <= 0.0)  // no errors, but less than equal to zero
      error ("Slide time for fm cannot be less than or equal to 0.\n%s\n%s", subtoken, original);
    fm1->slide_time = slide_time;
  }
  else if (subtoken != NULL)  // it's there, not slide, step, or vary, must be amp variation
  {
    errno = 0;
    double amp_beat1 = strtod (subtoken, &endptr);
    if ((amp_beat1 == 0.0 && strcmp (subtoken, endptr) == 0)
        || (*endptr != '\0')
        || errno != 0)
      error ("Amplitude beat1 for fm had an error.\n%s\n%s", subtoken, original);
    else if (amp_beat1 < 0.0)  // no errors, but less than zero
      error ("Amplitude beat1 for fm cannot be less than 0.\n%s\n%s", subtoken, original);
    if (fm1->channel != 2)  // not right channel only
      fm1->amp_beat1 = amp_beat1;
    else  // right channel only
      fm1->amp_beat1 = 0.0;

    subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
    errno = 0;
    double amp_beat2 = strtod (subtoken, &endptr);
    if ((amp_beat2 == 0.0 && strcmp (subtoken, endptr) == 0)
        || (*endptr != '\0')
        || errno != 0)
      error ("Amplitude beat2 for fm had an error.\n%s\n%s", subtoken, original);
    else if (amp_beat2 < 0.0)  // no errors, but less than zero
      error ("Amplitude beat2 for fm cannot be less than 0.\n%s\n%s", subtoken, original);
    if (fm1->channel != 1)  // not left channel only
      fm1->amp_beat2 = amp_beat2;
    else  // left channel only
      fm1->amp_beat2 = 0.0;

    subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
    errno = 0;
    double amp_pct1 = strtod (subtoken, &endptr);
    if ((amp_pct1 == 0.0 && strcmp (subtoken, endptr) == 0)
        || (*endptr != '\0')
        || errno != 0)
      error ("Amplitude adj1 for fm had an error.\n%s\n%s", subtoken, original);
    else if (amp_pct1 < 0.0)  // no errors, but less than zero
      error ("Amplitude adj1 for fm cannot be less than 0.\n%s\n%s", subtoken, original);
    if (fm1->channel != 2)  // not right channel only
      fm1->amp_pct1 = AMP_AD(amp_pct1);
    else  // right channel only
      fm1->amp_pct1 = 0.0;

    subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
    errno = 0;
    double amp_pct2 = strtod (subtoken, &endptr);
    if ((amp_pct2 == 0.0 && strcmp (subtoken, endptr) == 0)
        || (*endptr != '\0')
        || errno != 0)
      error ("Amplitude adj2 for fm had an error.\n%s\n%s", subtoken, original);
    else if (amp_pct2 < 0.0)  // no errors, but less than zero
      error ("Amplitude adj2 for fm cannot be less than 0.\n%s\n%s", subtoken, original);
    if (fm1->channel != 1)  // not left channel only
      fm1->amp_pct2 = AMP_AD(amp_pct2);
    else  // left channel only
      fm1->amp_pct2 = 0.0;

    /* check if there is a slide after amp beat */
    subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
    if (subtoken != NULL && strcmp (subtoken, ">") == 0)  // slide
      fm1->slide = 1;
    else if (subtoken != NULL && strcmp (subtoken, "&") == 0)  // step slide
    {
      fm1->type = 20;  // freq step
      fm1->slide = 2;  // freq step slide

      subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
      errno = 0;
      double steps = strtod (subtoken, &endptr);
      if ((steps == 0.0 && strcmp (subtoken, endptr) == 0)
          || (*endptr != '\0')
          || errno != 0)
        error ("Step count for fm had an error.\n%s\n%s", subtoken, original);
      else if (steps <= 0.0)  // no errors, but less than equal to zero
        error ("Step count for fm cannot be less than or equal to 0.\n%s\n%s", subtoken, original);
      fm1->steps = (int) steps;

      subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
      errno = 0;
      double slide_time = strtod (subtoken, &endptr);
      if ((slide_time == 0.0 && strcmp (subtoken, endptr) == 0)
          || (*endptr != '\0')
          || errno != 0)
        error ("Slide time for fm had an error.\n%s\n%s", subtoken, original);
      else if (slide_time <= 0.0)  // no errors, but less than equal to zero
        error ("Slide time for fm cannot be less than or equal to 0.\n%s\n%s", subtoken, original);
      fm1->slide_time = slide_time;

      subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
      errno = 0;
      double fuzz = strtod (subtoken, &endptr);
      if ((fuzz == 0.0 && strcmp (subtoken, endptr) == 0)
          || (*endptr != '\0')
          || errno != 0)
        error ("Fuzz for fm had an error.\n%s\n%s", subtoken, original);
      else if (fuzz < 0.0)  // no errors, but less than zero
        error ("Fuzz for fm cannot be less than 0.\n%s\n%s", subtoken, original);
      fm1->fuzz = AMP_AD(fuzz);
    }
    else if (subtoken != NULL && strcmp (subtoken, "~") == 0)  // vary
    {
      fm1->type = 21;  // freq vary
      fm1->slide = 3;  // freq vary slide

      subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
      errno = 0;
      double steps = strtod (subtoken, &endptr);
      if ((steps == 0.0 && strcmp (subtoken, endptr) == 0)
          || (*endptr != '\0')
          || errno != 0)
        error ("Step count for fm had an error.\n%s\n%s", subtoken, original);
      else if (steps <= 0.0)  // no errors, but less than equal to zero
        error ("Step count for fm cannot be less than or equal to 0.\n%s\n%s", subtoken, original);
      fm1->steps = (int) steps;

      subtoken = strtok_r (str2, separators, &saveptr2);        // get next subtoken
      errno = 0;
      double slide_time = strtod (subtoken, &endptr);
      if ((slide_time == 0.0 && strcmp (subtoken, endptr) == 0)
          || (*endptr != '\0')
          || errno != 0)
        error ("Slide time for fm had an error.\n%s\n%s", subtoken, original);
      else if (slide_time <= 0.0)  // no errors, but less than equal to zero
        error ("Slide time for fm cannot be less than or equal to 0.\n%s\n%s", subtoken, original);
      fm1->slide_time = slide_time;
    }
    else if (subtoken != NULL) // invalid slide indicator
      error ("Slide indicator for binaural had an error.\n%s\n%s", subtoken, original);
  }
}

/*  Initialize all values possible for each beat voice */

void
finish_beat_voice_setup ()
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
              if (stub2->type == 1 || stub2->type == 9 || stub2->type == 11)  // also binaural
              { 
                binaural2 = (binaural *) work2;
                /* Set the pointers to the previous voice's offsets here so it can be used while running.
                   Need to do this even when there is no slide.  Some duplication with below. */
                binaural2->last_off1 = &(binaural1->off1);
                binaural2->last_off2 = &(binaural1->off2);
                binaural2->last_amp_off1 = &(binaural1->amp_off1);
                binaural2->last_amp_off2 = &(binaural1->amp_off2);
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
            chronaural1->off1 = chronaural1->inc1 = chronaural1->off3 = chronaural1->inc3 = chronaural1->off2 = 0;
            chronaural1->inc2 = 0.0;
            if (work2 != NULL)
            { 
              stub2 = (stub *) work2;
              if (stub2->type == 8 || stub2->type == 10 || stub2->type == 12)  // also chronaural
              { 
                chronaural2 = (chronaural *) work2;
                /* Set the pointers to the previous voice's offsets here so it can be used while running.
                   Need to do this even when there is no slide. */
                chronaural2->last_off1 = &(chronaural1->off1);
                chronaural2->last_off3 = &(chronaural1->off3);
                chronaural2->last_off2 = &(chronaural1->off2);
                if (chronaural1->slide == 0)
                  (chronaural1->carr_adj = chronaural1->beat_adj = chronaural1->phase_adj
                                      = chronaural1->amp_adj = chronaural1->split_beat_adj = 0.0);
                else  // slide to next chronaural in stream
                {
                  chronaural1->carr_adj = (chronaural2->carrier - chronaural1->carrier)/ (double) snd1->tot_frames;
                  chronaural1->beat_adj = (chronaural2->beat - chronaural1->beat)/ (double) snd1->tot_frames;
                  chronaural1->phase_adj = (chronaural2->phase - chronaural1->phase)/ (double) snd1->tot_frames;
                  chronaural1->amp_adj = (chronaural2->amp - chronaural1->amp)/ (double) snd1->tot_frames;
                  chronaural1->split_beat_adj = (chronaural2->split_beat - chronaural1->split_beat) 
                                                                                            / (double) snd1->tot_frames;
                }
              } 
              else if (chronaural1->slide != 0)
                error ("Slide called for, voice to slide to is not chronaural.  Position matters!\n");
            } 
            else if (chronaural1->slide != 0)
              error ("Slide called for, no next chronaural in time sequence!\n");
            else
              chronaural1->split_beat_adj = 0.0;
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
            if (chronaural1->split_beat == 0.0 && chronaural1->split_beat_adj == 0.0)
                /* no split beat in this voice and not sliding to split beat in next voice, so pan */
              chronaural1->split_adj = ((chronaural1->split_end - chronaural1->split_begin) 
                                                              / (double) snd1->tot_frames);  // adjust per frame
            else  // is split beat
            {
              if (chronaural1->split_end < chronaural1->split_begin)  // end always larger for split beat, swap if not
              {
                double split_hold = chronaural1->split_begin;  // swap begin and end
                chronaural1->split_begin = chronaural1->split_end;
                chronaural1->split_end = split_hold;
              }
              double frames_per_cycle = ((double) out_rate / chronaural1->split_beat);  // frames in a back and forth cycle
                /* adjust to do that cycle, sign oscillates in generate_frames 
                 * Note that split_adj is being used differently than above, 
                 * There it is the adjustment to reach the end split over the course of the voice period.
                 * Here it is the adjustment so that the split oscillates between split_begin and split_end
                 * at the split_beat rate.  This works because the two are mutually exclusive. */
              chronaural1->split_adj = ((2.*(chronaural1->split_end - chronaural1->split_begin)) / frames_per_cycle);  
            }
            break;
          }
        case 9:  // binaural step slide, have to create list of steps and slides
          { 
            binaural *binaural1 = NULL, *binaural2 = NULL, *binaural3 = NULL, *binaural4 = NULL;

            binaural1 = (binaural *) work1;
            binaural1->off1 = binaural1->inc1 = binaural1->off2 = binaural1->inc2 = 0;
            binaural1->amp_off1 = binaural1->amp_inc1 = binaural1->amp_off2 = binaural1->amp_inc2 = 0;
             /* First step is always the input frequency, so no adjust. */
            binaural1->carr_adj = binaural1->beat_adj = binaural1->amp_adj = 0.0;
            binaural1->amp_beat1_adj = binaural1->amp_beat2_adj = 0.0;
            binaural1->amp_pct1_adj = binaural1->amp_pct2_adj = 0.0;
            /* Determine the step and slide frame sizes.  */
            int_64 slide_frames = (int_64) (out_rate * binaural1->slide_time);  // frames in each slide
            int_64 total_slide = (int_64) (slide_frames * binaural1->steps);  //  total slide time
            int_64 step_frames = (snd1->tot_frames - total_slide) / binaural1->steps;  // frames in each step
            /*  Leftover frames after all step slides determined.  Add to last step. The total number
             *  of frames in the list has to be exactly the number of frames in the current time sequence. */
            int_64 frame_residue = (snd1->tot_frames - total_slide - (step_frames * binaural1->steps));
            binaural1->tot_frames = step_frames;
            binaural1->cur_frames = 0;  // binaural1 complete except for step list pointer set below.
            if (work2 != NULL)  // determine binaural we are step sliding to so steps and slides can be set up
            { 
              stub2 = (stub *) work2;
              if (stub2->type == 1 || stub2->type == 9 || stub2->type == 11)  // also binaural
                binaural2 = (binaural *) work2;
              else
                error ("Step slide called for, voice to slide to is not binaural.  Position matters!\n");
            } 
            else
              error ("Step slide called for, no next binaural in time sequence!\n");
            double carr_diff = (binaural2->carrier - binaural1->carrier);
            double beat_diff = (binaural2->beat - binaural1->beat);
            double amp_diff = (binaural2->amp - binaural1->amp);
            double amp_beat1_diff = (binaural2->amp_beat1 - binaural1->amp_beat1);
            double amp_beat2_diff = (binaural2->amp_beat2 - binaural1->amp_beat2);
            double amp_pct1_diff = (binaural2->amp_pct1 - binaural1->amp_pct1);
            double amp_pct2_diff = (binaural2->amp_pct2 - binaural1->amp_pct2);
            double next_carrier = 0.0;
            double next_beat = 0.0;
            double next_amp = 0.0;
            double next_amp_beat1 = 0.0;
            double next_amp_beat2 = 0.0;
            double next_amp_pct1 = 0.0;
            double next_amp_pct2 = 0.0;
            binaural4 = binaural1;  // set last node processed
            int total_nodes = (2 * binaural1->steps);
            int ii;
            for (ii = 1; ii < total_nodes; ii++)  // create rest of step list nodes
            {
              binaural3 = (binaural *) Alloc ((sizeof (binaural)) * 1);  // create next node of step list
              if (ii % 2 == 1)  // a slide
              {
                memcpy ((void *) binaural3, (void *) binaural4, sizeof (binaural)); // copy last step
                binaural3->tot_frames = slide_frames;
                if (ii == total_nodes - 1)  // last slide, to next time sequence voice binaural2
                {
                  binaural2->last_off1 = &(binaural3->off1);
                  binaural2->last_off2 = &(binaural3->off2);
                  binaural2->last_amp_off1 = &(binaural3->amp_off1);
                  binaural2->last_amp_off2 = &(binaural3->amp_off2);
                  next_carrier = binaural2->carrier;
                  next_beat = binaural2->beat;
                  next_amp = binaural2->amp;
                  next_amp_beat1 = binaural2->amp_beat1;
                  next_amp_beat2 = binaural2->amp_beat2;
                  next_amp_pct1 = binaural2->amp_pct1;
                  next_amp_pct2 = binaural2->amp_pct2;
                  binaural3->step_next = NULL;  // last node, no next node
                }
                else  // internal slide
                {
                  double fraction = ((double) (ii+1)/(double) total_nodes);  // fraction of interval
                  next_carrier = binaural1->carrier + (carr_diff * fraction);
                  next_beat = binaural1->beat + (beat_diff * fraction);
                  next_amp = binaural1->amp + (amp_diff * fraction);
                  next_amp_beat1 = binaural1->amp_beat1 + (amp_beat1_diff * fraction);
                  next_amp_beat2 = binaural1->amp_beat2 + (amp_beat2_diff * fraction);
                  next_amp_pct1 = binaural1->amp_pct1 + (amp_pct1_diff * fraction);
                  next_amp_pct2 = binaural1->amp_pct2 + (amp_pct2_diff * fraction);
                  if (binaural1->fuzz > 0.0)  // fuzz the interval
                  {
                    double adjust = drand48() - 0.5;  // fuzz adjustment between -.5 and +.5 of fuzz
                    next_carrier += ((carr_diff/binaural1->steps) * binaural1->fuzz * adjust);
                    next_beat += ((beat_diff/binaural1->steps) * binaural1->fuzz * adjust);
                    next_amp += ((amp_diff/binaural1->steps) * binaural1->fuzz * adjust);
                    next_amp_beat1 += ((amp_beat1_diff/binaural1->steps) * binaural1->fuzz * adjust);
                    next_amp_beat2 += ((amp_beat2_diff/binaural1->steps) * binaural1->fuzz * adjust);
                    next_amp_pct1 += ((amp_pct1_diff/binaural1->steps) * binaural1->fuzz * adjust);
                    next_amp_pct2 += ((amp_pct2_diff/binaural1->steps) * binaural1->fuzz * adjust);
                  }
                }
                binaural3->carr_adj = (next_carrier - binaural4->carrier)/ binaural3->tot_frames;
                binaural3->beat_adj = (next_beat - binaural4->beat)/ binaural3->tot_frames;
                binaural3->amp_adj = (next_amp - binaural4->amp)/ binaural3->tot_frames;
                /* Amplitude beats are optional.  If there isn't a match, treat as zero instead */
                if (next_amp_beat1 > 0.0)
                  binaural3->amp_beat1_adj = (next_amp_beat1 - binaural4->amp_beat1)/ binaural3->tot_frames;
                else  // zero amp_beat1 in next binaural
                  binaural3->amp_beat1_adj = - binaural4->amp_beat1 / binaural3->tot_frames;
                if (next_amp_beat2 > 0.0)
                  binaural3->amp_beat2_adj = (next_amp_beat2 - binaural4->amp_beat2)/ binaural3->tot_frames;
                else  // zero amp_beat2 in next binaural
                  binaural3->amp_beat2_adj = - binaural4->amp_beat2 / binaural3->tot_frames;
                /* Amplitude percents are optional.  If there isn't a match, treat as zero instead */
                if (next_amp_pct1 > 0.0)
                  binaural3->amp_pct1_adj = (next_amp_pct1 - binaural4->amp_pct1)/ binaural3->tot_frames;
                else  // zero amp_pct1 in next binaural
                  binaural3->amp_pct1_adj = - binaural4->amp_pct1 / binaural3->tot_frames;
                if (next_amp_pct2 > 0.0)
                  binaural3->amp_pct2_adj = (next_amp_pct2 - binaural4->amp_pct2)/ binaural3->tot_frames;
                else  // zero amp_pct2 in next binaural
                  binaural3->amp_pct2_adj = - binaural4->amp_pct2 / binaural3->tot_frames;
              } 
              else  // a step
              {
                memcpy ((void *) binaural3, (void *) binaural1, sizeof (binaural)); // copy first in list to it
                if (ii == (total_nodes - 2))
                  binaural3->tot_frames += frame_residue;  // use up leftover frames in last step
                /* Set values used for calculation in last slide */
                binaural3->carrier = next_carrier;
                binaural3->beat = next_beat;
                binaural3->amp = next_amp;
                binaural3->amp_beat1 = next_amp_beat1;
                binaural3->amp_beat2 = next_amp_beat2;
                binaural3->amp_pct1 = next_amp_pct1;
                binaural3->amp_pct2 = next_amp_pct2;
              }
              binaural4->step_next = binaural3;  // set list pointer for previous node
              binaural3->last_off1 = &(binaural4->off1);  // each node starts where last left off as offset
              binaural3->last_off2 = &(binaural4->off2);
              binaural3->last_amp_off1 = &(binaural4->amp_off1);  // each node starts where last left off as amp_offset
              binaural3->last_amp_off2 = &(binaural4->amp_off2);
              binaural4 = binaural3;  // make current node previous node
            }
            break;
          }
        case 10:  // chronaural step slide, have to create list of steps and slides
          { 
            chronaural *chronaural1 = NULL, *chronaural2 = NULL, *chronaural3 = NULL, *chronaural4 = NULL;

            chronaural1 = (chronaural *) work1;
            chronaural1->off1 = chronaural1->inc1 = chronaural1->off3 = chronaural1->inc3 = chronaural1->off2 = 0;
            chronaural1->inc2 = 0.0;
             /* First step is always the input frequency, so no adjust. */
            chronaural1->carr_adj = chronaural1->beat_adj = chronaural1->phase_adj = chronaural1->amp_adj = 0.0;
            chronaural1->split_beat_adj = chronaural1->split_adj = 0.0;
            /* Determine the step and slide frame sizes.  */
            int_64 slide_frames = (int_64) (out_rate * chronaural1->slide_time);  // frames in each slide
            int_64 total_slide = (int_64) (slide_frames * chronaural1->steps);  //  total slide frames
            int_64 step_frames = (snd1->tot_frames - total_slide) / chronaural1->steps;  // frames in each step
            /*  Leftover frames after all step slides determined.  Add to last step. The total number
             *  of frames in the list has to be exactly the number of frames in the current time sequence. */
            int_64 frame_residue = (snd1->tot_frames - total_slide - (step_frames * chronaural1->steps));
            chronaural1->tot_frames = step_frames;
            chronaural1->cur_frames = 0;  // chronaural1 complete except for step list pointer set below.
            if (work2 != NULL)  // determine chronaural we are step sliding to so steps and slides can be set up
            { 
              stub2 = (stub *) work2;
              if (stub2->type == 8 || stub2->type == 10 || stub2->type == 12)  // also chronaural
                chronaural2 = (chronaural *) work2;
              else
                error ("Step slide called for, voice to slide to is not chronaural.  Position matters!\n");
            } 
            else
              error ("Step slide called for, no next chronaural in time sequence!\n");
            double carr_diff = (chronaural2->carrier - chronaural1->carrier);
            double beat_diff = (chronaural2->beat - chronaural1->beat);
            double phase_diff = (chronaural2->phase - chronaural1->phase);
            double amp_diff = (chronaural2->amp - chronaural1->amp);
            double split_beat_diff = (chronaural2->split_beat - chronaural1->split_beat);
            double next_carrier = 0.0;
            double next_beat = 0.0;
            double next_phase = 0.0;
            double next_amp = 0.0;
            double next_split_beat = 0.0;
            chronaural4 = chronaural1;  // set last node processed
            int total_nodes = (2 * chronaural1->steps);
            int ii;
            for (ii = 1; ii < total_nodes; ii++)  // create rest of step list nodes
            {
              chronaural3 = (chronaural *) Alloc ((sizeof (chronaural)) * 1);  // create next node of step list
              if (ii % 2 == 1)  // a slide
              {
                memcpy ((void *) chronaural3, (void *) chronaural4, sizeof (chronaural)); // copy last step
                chronaural3->tot_frames = slide_frames;
                if (ii == total_nodes - 1)  // last slide, to next time sequence voice chronaural2
                {
                  chronaural2->last_off1 = &(chronaural3->off1);
                  chronaural2->last_off3 = &(chronaural3->off3);
                  chronaural2->last_off2 = &(chronaural3->off2);
                  next_carrier = chronaural2->carrier;
                  next_beat = chronaural2->beat;
                  next_phase = chronaural2->phase;
                  next_amp = chronaural2->amp;
                  chronaural3->step_next = NULL;  // last node, no next node
                }
                else  // internal slide
                {
                  double fraction = ((double) (ii+1)/(double) total_nodes);  // fraction of interval
                  next_carrier = chronaural1->carrier + (carr_diff * fraction);
                  next_beat = chronaural1->beat + (beat_diff * fraction);
                  next_phase = chronaural1->phase + (phase_diff * fraction);
                  next_amp = chronaural1->amp + (amp_diff * fraction);
                  next_split_beat = chronaural1->split_beat + (split_beat_diff * fraction);
                  if (chronaural1->fuzz > 0.0)  // fuzz the interval
                  {
                    double adjust = drand48() - 0.5;  // fuzz adjustment between -.5 and +.5 of fuzz
                    next_carrier += ((carr_diff/chronaural1->steps) * chronaural1->fuzz * adjust);
                    next_beat += ((beat_diff/chronaural1->steps) * chronaural1->fuzz * adjust);
                    next_phase += ((phase_diff/chronaural1->steps) * chronaural1->fuzz * adjust);
                    next_amp += ((amp_diff/chronaural1->steps) * chronaural1->fuzz * adjust);
                  }
                }
                chronaural3->carr_adj = (next_carrier - chronaural4->carrier)/ chronaural3->tot_frames;
                chronaural3->beat_adj = (next_beat - chronaural4->beat)/ chronaural3->tot_frames;
                chronaural3->phase_adj = (next_phase - chronaural4->phase)/ chronaural3->tot_frames;
                chronaural3->amp_adj = (next_amp - chronaural4->amp)/ chronaural3->tot_frames;
                   /* change split beat only in slides */
                chronaural3->split_beat_adj = (next_split_beat - chronaural4->split_beat)/ chronaural3->tot_frames;
              } 
              else  // a step
              {
                memcpy ((void *) chronaural3, (void *) chronaural1, sizeof (chronaural)); // copy first in list to it
                if (ii == (total_nodes - 2))
                  chronaural3->tot_frames += frame_residue;  // use up leftover frames in last step
                /* Set values used for calculation in last slide */
                chronaural3->carrier = next_carrier;
                chronaural3->beat = next_beat;
                chronaural3->phase = next_phase;
                chronaural3->amp = next_amp;
                chronaural3->split_beat = next_split_beat;
                chronaural3->split_beat_adj = 0.0;  //steps are constant
              }
                /* Set up the split logic here as it applies throughout the voice period.
                 * Use chronaural1 to determine branching as it won't be changed until list is complete.
                   Don't need to worry about overwriting begin and end splits as they are only used once
                   Same logic for slides and steps */
              if (chronaural1->split_begin == -1.0)  // chronaural split start random
              {
                if (chronaural4 != chronaural1)  // previous node not first node in chain
                  chronaural3->split_begin = chronaural4->split_end; // begin split is previous node end split
                else  // first node after start of chain
                {  /* begin split is random and will become first nodes end split below */
                  double delta = ( (drand48 ()) * (chronaural1->split_high - chronaural1->split_low));
                  chronaural3->split_begin = chronaural1->split_low + delta;
                }
              }
              chronaural3->split_now = chronaural3->split_begin;      // set working split to begin
              if (chronaural1->split_end == -1.0)  // chronaural split end random
              {
                if (ii == total_nodes - 1)  // last slide, to next time sequence voice chronaural2
                {
                  if (chronaural2->split_begin == -1.0)  //random
                  {
                    double delta = ( (drand48 ()) * (chronaural1->split_high - chronaural1->split_low));
                    chronaural3->split_end = chronaural1->split_low + delta; // end split for this chronaural
                    chronaural2->split_begin = chronaural3->split_end;  // set this as begin split for next voice
                  }
                  else  // fixed split in next voice
                    chronaural3->split_end = chronaural2->split_begin; // ending split is next voice begin split
                }
                else  // internal 
                {
                  double delta = ( (drand48 ()) * (chronaural1->split_high - chronaural1->split_low));
                  chronaural3->split_end = chronaural1->split_low + delta;      // ending split for chronaural
                }
              }
              if (split_beat_diff == 0.0 && chronaural1->split_beat == 0.0)
                  /* no split beat in this voice and not sliding to split beat in next voice, perform pan */
                chronaural3->split_adj = ((chronaural3->split_end - chronaural3->split_begin) 
                                                        / (double) chronaural3->tot_frames);  // adjust per frame
              else
              {
                if (chronaural3->split_end < chronaural3->split_begin)  // end always larger for split beat, swap if not
                {
                  double split_hold = chronaural3->split_begin;  // swap begin and end
                  chronaural3->split_begin = chronaural3->split_end;
                  chronaural3->split_end = split_hold;
                }
                double frames_per_cycle = ((double) out_rate / chronaural3->split_beat);  // frames in a back and forth cycle
                  /* adjust to do that cycle, sign oscillates in generate_frames 
                   * Note that split_adj is being used differently than above, 
                   * There it is the adjustment to reach the end split over the course of the voice period.
                   * Here it is the adjustment so that the split oscillates between split_begin and split_end
                   * at the split_beat rate.  This works because the two are mutually exclusive. */
                chronaural3->split_adj = ((2.*(chronaural3->split_end - chronaural3->split_begin)) / frames_per_cycle);  
              }
              chronaural4->step_next = chronaural3;  // set list pointer for previous node
              chronaural3->last_off1 = &(chronaural4->off1);  // each node starts where last left off as offset
              chronaural3->last_off3 = &(chronaural4->off3);  // each node starts where last left off as offset
              chronaural3->last_off2 = &(chronaural4->off2);
              chronaural4 = chronaural3;  // make current node previous node
            }
              /* Now set up the split logic for chronaural1 as it applies throughout the voice period.
                 Don't need to worry about overwriting begin and end splits as they are only used once
                 and the rest of the step slide list is done */
            if (chronaural1->split_begin == -1.0)  // chronaural split start random
            {
              double delta = ( (drand48 ()) * (chronaural1->split_high - chronaural1->split_low));
              chronaural1->split_begin = chronaural1->split_low + delta;      // starting split for chronaural
            }
            chronaural1->split_now = chronaural1->split_begin;      // set working split to begin
            if (chronaural1->split_end == -1.0)  // chronaural split end random
                /* end split for this chronaural is begin split from next chronaural in chain set above */
              chronaural1->split_end = chronaural1->step_next->split_begin;
            if (split_beat_diff == 0.0 && chronaural1->split_beat == 0.0)
                /* no split beat in this voice and not sliding to split beat in next voice, so pan */
              chronaural1->split_adj = ((chronaural1->split_end - chronaural1->split_begin) 
                                        / (double) chronaural1->tot_frames);  // adjust per frame
            else  // split beat
            {
              if (chronaural1->split_end < chronaural1->split_begin)  // end always larger for split beat, swap if not
              {
                double split_hold = chronaural1->split_begin;  // swap begin and end
                chronaural1->split_begin = chronaural1->split_end;
                chronaural1->split_end = split_hold;
              }
              double frames_per_cycle = ((double) out_rate / chronaural1->split_beat);  // frames in a back and forth cycle
                /* adjust to do the cycle, sign oscillates in generate_frames 
                 * Note that split_adj is being used differently than above, 
                 * There it is the adjustment to reach the end split over the course of the voice period.
                 * Here it is the adjustment so that the split oscillates between split_begin and split_end
                 * at the split_beat rate.  This works because the two are mutually exclusive. */
              chronaural1->split_adj = (2. * (chronaural1->split_end - chronaural1->split_begin) / frames_per_cycle);  
            }
            break;
          }
        case 11:  // binaural vary slide, have to create list of steps and slides
          { 
            binaural *binaural1 = NULL, *binaural2 = NULL, *binaural3 = NULL, *binaural4 = NULL;

            binaural1 = (binaural *) work1;
            binaural1->off1 = binaural1->inc1 = binaural1->off2 = binaural1->inc2 = 0;
            binaural1->amp_off1 = binaural1->amp_inc1 = binaural1->amp_off2 = binaural1->amp_inc2 = 0;
             /* First step is always the input frequency, so no adjust. */
            binaural1->carr_adj = binaural1->beat_adj = binaural1->amp_adj = 0.0;
            binaural1->amp_beat1_adj = binaural1->amp_beat2_adj = 0.0;
            binaural1->amp_pct1_adj = binaural1->amp_pct2_adj = 0.0;
            /* Determine the step and slide frame sizes.  */
            int_64 slide_frames = (int_64) (out_rate * binaural1->slide_time);  // frames in each slide
            int_64 total_slide = (int_64) (slide_frames * binaural1->steps);  //  total slide time
            int_64 step_frames = (snd1->tot_frames - total_slide) / binaural1->steps;  // frames in each step
            /*  Leftover frames after all step slides determined.  Add to last slide. The total number
             *  of frames in the list has to be exactly the number of frames in the current time sequence. */
            int_64 frame_residue = (snd1->tot_frames - total_slide - (step_frames * binaural1->steps));
            binaural1->tot_frames = step_frames;
            binaural1->cur_frames = 0;  // binaural1 complete except for step list pointer set below.
            if (work2 != NULL)  // determine binaural we are step sliding to so steps and slides can be set up
            { 
              stub2 = (stub *) work2;
              if (stub2->type == 1 || stub2->type == 9 || stub2->type == 11)  // also binaural
                binaural2 = (binaural *) work2;
              else
                error ("Step slide called for, voice to slide to is not binaural.  Position matters!\n");
            } 
            else
              error ("Step slide called for, no next binaural in time sequence!\n");
            double carr_diff = (binaural2->carrier - binaural1->carrier);
            double beat_diff = (binaural2->beat - binaural1->beat);
            double amp_diff = (binaural2->amp - binaural1->amp);
            double amp_beat1_diff = (binaural2->amp_beat1 - binaural1->amp_beat1);
            double amp_beat2_diff = (binaural2->amp_beat2 - binaural1->amp_beat2);
            double amp_pct1_diff = (binaural2->amp_pct1 - binaural1->amp_pct1);
            double amp_pct2_diff = (binaural2->amp_pct2 - binaural1->amp_pct2);
            double next_carrier = 0.0;
            double next_beat = 0.0;
            double next_amp = 0.0;
            double next_amp_beat1 = 0.0;
            double next_amp_beat2 = 0.0;
            double next_amp_pct1 = 0.0;
            double next_amp_pct2 = 0.0;
            binaural4 = binaural1;  // set last node processed
            int total_nodes = (2 * binaural1->steps);
            int ii;
            for (ii = 1; ii < total_nodes; ii++)  // create rest of vary list nodes
            {
              binaural3 = (binaural *) Alloc ((sizeof (binaural)) * 1);  // create next node of vary list
              if (ii % 2 == 1)  // a slide
              {
                memcpy ((void *) binaural3, (void *) binaural4, sizeof (binaural)); // copy last step
                binaural3->tot_frames = slide_frames;
                if (ii == total_nodes - 1)  // last slide, to next time sequence voice binaural2
                {
                  binaural2->last_off1 = &(binaural3->off1);  // binaural2 will start from these offsets
                  binaural2->last_off2 = &(binaural3->off2);
                  binaural2->last_amp_off1 = &(binaural3->amp_off1);  // binaural2 will start from these amp_offsets
                  binaural2->last_amp_off2 = &(binaural3->amp_off2);
                  next_carrier = binaural2->carrier;
                  next_beat = binaural2->beat;
                  next_amp = binaural2->amp;
                  next_amp_beat1 = binaural2->amp_beat1;
                  next_amp_beat2 = binaural2->amp_beat2;
                  next_amp_pct1 = binaural2->amp_pct1;
                  next_amp_pct2 = binaural2->amp_pct2;
                  binaural3->step_next = NULL;  // last node, no next node
                  binaural3->tot_frames += frame_residue;  // use up leftover frames in last slide
                }
                else  // internal slide
                {
                  double fraction = drand48 ();  // random fraction of interval
                  next_carrier = binaural1->carrier + (carr_diff * fraction);
                  next_beat = binaural1->beat + (beat_diff * fraction);
                  next_amp = binaural1->amp + (amp_diff * fraction);
                  next_amp_beat1 = binaural1->amp_beat1 + (amp_beat1_diff * fraction);
                  next_amp_beat2 = binaural1->amp_beat2 + (amp_beat2_diff * fraction);
                  next_amp_pct1 = binaural1->amp_pct1 + (amp_pct1_diff * fraction);
                  next_amp_pct2 = binaural1->amp_pct2 + (amp_pct2_diff * fraction);
                }
                binaural3->carr_adj = (next_carrier - binaural4->carrier)/ binaural3->tot_frames;
                binaural3->beat_adj = (next_beat - binaural4->beat)/ binaural3->tot_frames;
                binaural3->amp_adj = (next_amp - binaural4->amp)/ binaural3->tot_frames;
                /* Amplitude beats are optional.  If there isn't a match, treat as zero instead */
                if (next_amp_beat1 > 0.0)
                  binaural3->amp_beat1_adj = (next_amp_beat1 - binaural4->amp_beat1)/ binaural3->tot_frames;
                else  // zero amp_beat1 in next binaural
                  binaural3->amp_beat1_adj = - binaural4->amp_beat1 / binaural3->tot_frames;
                if (next_amp_beat2 > 0.0)
                  binaural3->amp_beat2_adj = (next_amp_beat2 - binaural4->amp_beat2)/ binaural3->tot_frames;
                else  // zero amp_beat2 in next binaural
                  binaural3->amp_beat2_adj = - binaural4->amp_beat2 / binaural3->tot_frames;
                /* Amplitude percents are optional.  If there isn't a match, treat as zero instead */
                if (next_amp_pct1 > 0.0)
                  binaural3->amp_pct1_adj = (next_amp_pct1 - binaural4->amp_pct1)/ binaural3->tot_frames;
                else  // zero amp_pct1 in next binaural
                  binaural3->amp_pct1_adj = - binaural4->amp_pct1 / binaural3->tot_frames;
                if (next_amp_pct2 > 0.0)
                  binaural3->amp_pct2_adj = (next_amp_pct2 - binaural4->amp_pct2)/ binaural3->tot_frames;
                else  // zero amp_pct2 in next binaural
                  binaural3->amp_pct2_adj = - binaural4->amp_pct2 / binaural3->tot_frames;
              } 
              else  // a step
              {
                memcpy ((void *) binaural3, (void *) binaural1, sizeof (binaural)); // copy first in list to it
                /* Set values used for calculation in last slide */
                binaural3->carrier = next_carrier;
                binaural3->beat = next_beat;
                binaural3->amp = next_amp;
                binaural3->amp_beat1 = next_amp_beat1;
                binaural3->amp_beat2 = next_amp_beat2;
                binaural3->amp_pct1 = next_amp_pct1;
                binaural3->amp_pct2 = next_amp_pct2;
              }
              binaural4->step_next = binaural3;  // set list pointer for previous node
              binaural3->last_off1 = &(binaural4->off1);  // each node starts where last left off as offset
              binaural3->last_off2 = &(binaural4->off2);
              binaural3->last_amp_off1 = &(binaural4->amp_off1);  // each node starts where last left off as amp_offset
              binaural3->last_amp_off2 = &(binaural4->amp_off2);
              binaural4 = binaural3;  // make current node previous node
            }
            break;
          }
        case 12:  // chronaural vary slide, have to create list of steps and slides
          { 
            chronaural *chronaural1 = NULL, *chronaural2 = NULL, *chronaural3 = NULL, *chronaural4 = NULL;

            chronaural1 = (chronaural *) work1;
            chronaural1->off1 = chronaural1->inc1 = chronaural1->off3 = chronaural1->inc3 = chronaural1->off2 = 0;
            chronaural1->inc2 = 0.0;
             /* First step is always the input frequency, so no adjust. */
            chronaural1->carr_adj = chronaural1->beat_adj = chronaural1->phase_adj = chronaural1->amp_adj = 0.0;
            chronaural1->split_beat_adj = chronaural1->split_adj = 0.0;
            /* Determine the step and slide frame sizes.  */
            int_64 slide_frames = (int_64) (out_rate * chronaural1->slide_time);  // frames in each slide
            int_64 total_slide = (int_64) (slide_frames * chronaural1->steps);  //  total slide frames
            int_64 step_frames = (snd1->tot_frames - total_slide) / chronaural1->steps;  // frames in each step
            /*  Leftover frames after all step slides determined.  Add to last slide. The total number
             *  of frames in the list has to be exactly the number of frames in the current time sequence. */
            int_64 frame_residue = (snd1->tot_frames - total_slide - (step_frames * chronaural1->steps));
            chronaural1->tot_frames = step_frames;
            chronaural1->cur_frames = 0;  // chronaural1 complete except for step list pointer set below.
            if (work2 != NULL)  // determine chronaural we are step sliding to so steps and slides can be set up
            { 
              stub2 = (stub *) work2;
              if (stub2->type == 8 || stub2->type == 10 || stub2->type == 12)  // also chronaural
                chronaural2 = (chronaural *) work2;
              else
                error ("Step slide called for, voice to slide to is not chronaural.  Position matters!\n");
            } 
            else
              error ("Step slide called for, no next chronaural in time sequence!\n");
            double carr_diff = (chronaural2->carrier - chronaural1->carrier);
            double beat_diff = (chronaural2->beat - chronaural1->beat);
            double phase_diff = (chronaural2->phase - chronaural1->phase);
            double amp_diff = (chronaural2->amp - chronaural1->amp);
            double split_beat_diff = (chronaural2->split_beat - chronaural1->split_beat);
            double next_carrier = 0.0;
            double next_beat = 0.0;
            double next_phase = 0.0;
            double next_amp = 0.0;
            double next_split_beat = 0.0;
            chronaural4 = chronaural1;  // set last node processed
            int total_nodes = (2 * chronaural1->steps);
            int ii;
            for (ii = 1; ii < total_nodes; ii++)  // create rest of step list nodes
            {
              chronaural3 = (chronaural *) Alloc ((sizeof (chronaural)) * 1);  // create next node of step list
              if (ii % 2 == 1)  // a slide
              {
                memcpy ((void *) chronaural3, (void *) chronaural4, sizeof (chronaural)); // copy last step
                chronaural3->tot_frames = slide_frames;
                if (ii == total_nodes - 1)  // last slide, to next time sequence voice chronaural2
                {
                  chronaural2->last_off1 = &(chronaural3->off1);
                  chronaural2->last_off3 = &(chronaural3->off3);
                  chronaural2->last_off2 = &(chronaural3->off2);
                  next_carrier = chronaural2->carrier;
                  next_beat = chronaural2->beat;
                  next_phase = chronaural2->phase;
                  next_amp = chronaural2->amp;
                  chronaural3->step_next = NULL;  // last node, no next node
                }
                else  // internal slide
                {
                  double fraction = drand48 ();  // random fraction of interval
                  next_carrier = chronaural1->carrier + (carr_diff * fraction);
                  next_beat = chronaural1->beat + (beat_diff * fraction);
                  next_phase = chronaural1->phase + (phase_diff * fraction);
                  next_amp = chronaural1->amp + (amp_diff * fraction);
                  next_split_beat = chronaural1->split_beat + (split_beat_diff * fraction);
                }
                chronaural3->carr_adj = (next_carrier - chronaural4->carrier)/ chronaural3->tot_frames;
                chronaural3->beat_adj = (next_beat - chronaural4->beat)/ chronaural3->tot_frames;
                chronaural3->phase_adj = (next_phase - chronaural4->phase)/ chronaural3->tot_frames;
                chronaural3->amp_adj = (next_amp - chronaural4->amp)/ chronaural3->tot_frames;
                   /* change split beat only in slides */
                chronaural3->split_beat_adj = (next_split_beat - chronaural4->split_beat)/ chronaural3->tot_frames;
              } 
              else  // a step
              {
                memcpy ((void *) chronaural3, (void *) chronaural1, sizeof (chronaural)); // copy first in list to it
                if (ii == (total_nodes - 2))
                  chronaural3->tot_frames += frame_residue;  // use up leftover frames in last step
                /* Set values used for calculation in last slide */
                chronaural3->carrier = next_carrier;
                chronaural3->beat = next_beat;
                chronaural3->phase = next_phase;
                chronaural3->amp = next_amp;
                chronaural3->split_beat = next_split_beat;
                chronaural3->split_beat_adj = 0.0;  //steps are constant
              }
                /* Set up the split logic here as it applies throughout the voice period for both slide and step.
                 * Use chronaural1 to determine branching as it won't be changed until list is complete.
                   Don't need to worry about overwriting begin and end splits as they are only used once
                   Same logic for slides and steps */
              if (chronaural1->split_begin == -1.0)  // chronaural split start random
              {
                if (chronaural4 != chronaural1)  // previous node not first node in chain
                  chronaural3->split_begin = chronaural4->split_end; // begin split is previous node end split
                else  // first node after start of chain
                {  /* begin split is random and will become first nodes end split below */
                  double delta = ( (drand48 ()) * (chronaural1->split_high - chronaural1->split_low));
                  chronaural3->split_begin = chronaural1->split_low + delta;
                }
              }
              chronaural3->split_now = chronaural3->split_begin;      // set working split to begin
              if (chronaural1->split_end == -1.0)  // chronaural split end random
              {
                if (ii == total_nodes - 1)  // last slide, to next time sequence voice chronaural2
                {
                  if (chronaural2->split_begin == -1.0)  //random
                  {
                    double delta = ( (drand48 ()) * (chronaural1->split_high - chronaural1->split_low));
                    chronaural3->split_end = chronaural1->split_low + delta; // end split for this chronaural
                    chronaural2->split_begin = chronaural3->split_end;  // set this as begin split for next voice
                  }
                  else  // fixed split in next voice
                    chronaural3->split_end = chronaural2->split_begin; // ending split is next voice begin split
                }
                else  // internal 
                {
                  double delta = ( (drand48 ()) * (chronaural1->split_high - chronaural1->split_low));
                  chronaural3->split_end = chronaural1->split_low + delta;      // ending split for chronaural
                }
              }
              if (split_beat_diff == 0.0 && chronaural1->split_beat == 0.0)
                  /* no split beat in this voice and not sliding to split beat in next voice, so pan */
                chronaural3->split_adj = ((chronaural3->split_end - chronaural3->split_begin) 
                                                        / (double) chronaural3->tot_frames);  // adjust per frame
              else
              {
                if (chronaural3->split_end < chronaural3->split_begin)  // end always larger for split beat, swap if not
                {
                  double split_hold = chronaural3->split_begin;  // swap begin and end
                  chronaural3->split_begin = chronaural3->split_end;
                  chronaural3->split_end = split_hold;
                }
                double frames_per_cycle = ((double) out_rate / chronaural3->split_beat);  // frames in a back and forth cycle
                  /* adjust to do that cycle, sign oscillates in generate_frames 
                   * Note that split_adj is being used differently than above, 
                   * There it is the adjustment to reach the end split over the course of the voice period.
                   * Here it is the adjustment so that the split oscillates between split_begin and split_end
                   * at the split_beat rate.  This works because the two are mutually exclusive. */
                chronaural3->split_adj = ((2.*(chronaural3->split_end - chronaural3->split_begin)) / frames_per_cycle);  
              }
              chronaural4->step_next = chronaural3;  // set list pointer for previous node
              chronaural3->last_off1 = &(chronaural4->off1);  // each node starts where last left off as offset
              chronaural3->last_off3 = &(chronaural4->off3);  // each node starts where last left off as offset
              chronaural3->last_off2 = &(chronaural4->off2);
              chronaural4 = chronaural3;  // make current node previous node
            }
              /* Now set up the split logic for chronaural1 as it applies throughout the voice period.
                 Don't need to worry about overwriting begin and end splits as they are only used once
                 and the rest of the step slide list is done */
            if (chronaural1->split_begin == -1.0)  // chronaural split start random
            {
              double delta = ( (drand48 ()) * (chronaural1->split_high - chronaural1->split_low));
              chronaural1->split_begin = chronaural1->split_low + delta;      // starting split for chronaural
            }
            chronaural1->split_now = chronaural1->split_begin;      // set working split to begin
            if (chronaural1->split_end == -1.0)  // chronaural split end random
                /* end split for this chronaural is begin split from next chronaural in chain set above */
              chronaural1->split_end = chronaural1->step_next->split_begin;
            if (split_beat_diff == 0.0 && chronaural1->split_beat == 0.0)
                /* no split beat in this voice and not sliding to split beat in next voice, so pan */
              chronaural1->split_adj = ((chronaural1->split_end - chronaural1->split_begin) 
                                        / (double) chronaural1->tot_frames);  // adjust per frame
            else  // split beat
            {
              if (chronaural1->split_end < chronaural1->split_begin)  // end always larger for split beat, swap if not
              {
                double split_hold = chronaural1->split_begin;  // swap begin and end
                chronaural1->split_begin = chronaural1->split_end;
                chronaural1->split_end = split_hold;
              }
              double frames_per_cycle = ((double) out_rate / chronaural1->split_beat);  // frames in a back and forth cycle
                /* adjust to do the cycle, sign oscillates in generate_frames 
                 * Note that split_adj is being used differently than above, 
                 * There it is the adjustment to reach the end split over the course of the voice period.
                 * Here it is the adjustment so that the split oscillates between split_begin and split_end
                 * at the split_beat rate.  This works because the two are mutually exclusive. */
              chronaural1->split_adj = (2. * (chronaural1->split_end - chronaural1->split_begin) / frames_per_cycle);  
            }
            break;
          }
        case 13:  // pulse
          {
            pulse *pulse1 = NULL, *pulse2 = NULL;

            pulse1 = (pulse *) work1;
            pulse1->off1 = pulse1->inc1 = pulse1->off3 = pulse1->inc3 = pulse1->off2 = 0;
            pulse1->inc2 = 0.0;
            if (work2 != NULL)
            { 
              stub2 = (stub *) work2;
              if (stub2->type == 13 || stub2->type == 14 || stub2->type == 15)  // also pulse
              { 
                pulse2 = (pulse *) work2;
                /* Set the pointers to the previous voice's offsets here so it can be used while running.
                   Need to do this even when there is no slide. */
                pulse2->last_off1 = &(pulse1->off1);
                pulse2->last_off3 = &(pulse1->off3);
                pulse2->last_off2 = &(pulse1->off2);
                if (pulse1->slide == 0)
                  (pulse1->carr_adj = pulse1->beat_adj = pulse1->phase_adj = pulse1->time_adj
                                      = pulse1->amp_adj = pulse1->split_beat_adj = 0.0);
                else  // slide to next pulse in stream
                {
                  pulse1->carr_adj = (pulse2->carrier - pulse1->carrier)/ (double) snd1->tot_frames;
                  pulse1->beat_adj = (pulse2->beat - pulse1->beat)/ (double) snd1->tot_frames;
                  pulse1->phase_adj = (pulse2->phase - pulse1->phase)/ (double) snd1->tot_frames;
                  pulse1->time_adj = (pulse2->time - pulse1->time)/ (double) snd1->tot_frames;
                  pulse1->amp_adj = (pulse2->amp - pulse1->amp)/ (double) snd1->tot_frames;
                  pulse1->split_beat_adj = (pulse2->split_beat - pulse1->split_beat) / (double) snd1->tot_frames;
                }
              } 
              else if (pulse1->slide != 0)
                error ("Slide called for, voice to slide to is not pulse.  Position matters!\n");
            } 
            else if (pulse1->slide != 0)
              error ("Slide called for, no next pulse in time sequence!\n");
            else
              pulse1->split_beat_adj = 0.0;
              /* set up the split logic here as it applies throughout the voice period.
                 don't need to worry about overwriting begin and end splits as they are only used once */
            if (pulse1->split_begin == -1.0)  // pulse split start random
            {
              double delta = ( (drand48 ()) * (pulse1->split_high - pulse1->split_low));
              pulse1->split_begin = pulse1->split_low + delta;      // starting split for pulse
            }
            pulse1->split_now = pulse1->split_begin;      // set working split to begin
            if (pulse1->split_end == -1.0)  // pulse split end random
            {
              double delta = ( (drand48 ()) * (pulse1->split_high - pulse1->split_low));
              pulse1->split_end = pulse1->split_low + delta;      // ending split for pulse
              while (fabs (pulse1->split_begin - pulse1->split_end) == 0.0)
              {  // difference equal to zero?  Repeat until larger.  
                delta = ( (drand48 ()) * (pulse1->split_high - pulse1->split_low));
                pulse1->split_end = pulse1->split_low + delta;      // ending split for pulse
              }
            }
            if (pulse1->split_beat == 0.0 && pulse1->split_beat_adj == 0.0)
            {
                /* No split beat in this voice and not sliding to split beat in next voice, so pan.
                 * The pan can go from left to right or right to left. */
              pulse1->split_dist = 0.0;  // set split distance to zero, not used to generate frames for pan
              pulse1->split_adj = ((pulse1->split_end - pulse1->split_begin) 
                                                              / (double) snd1->tot_frames);  // adjust per frame
            }
            else  // is split beat, split_begin and split_end are constant for duration of voice node
            {
              if (pulse1->split_end < pulse1->split_begin)  // end always larger for split beat, swap if not
              {
                double split_hold = pulse1->split_begin;  // swap begin and end
                pulse1->split_begin = pulse1->split_end;
                pulse1->split_end = split_hold;
                pulse1->split_now = pulse1->split_begin; // set working split to the new begin
              }
              pulse1->split_dist = pulse1->split_end - pulse1->split_begin;  // set split distance to the difference
              double frames_per_cycle = ((double) out_rate / pulse1->split_beat);  // frames in a back and forth cycle
                /* adjust to do that cycle, sign oscillates in generate_frames 
                 * Note that split_adj is being used differently than above, 
                 * There it is the adjustment to reach the end split over the course of the voice period.
                 * Here it is the adjustment so that the split oscillates between split_begin and split_end
                 * at the split_beat rate.  This works because the two are mutually exclusive. */
              pulse1->split_adj = ((2.*(pulse1->split_dist)) / frames_per_cycle);  
            }
            break;
          }
        case 14:  // pulse step slide, have to create list of steps and slides
          { 
            pulse *pulse1 = NULL, *pulse2 = NULL, *pulse3 = NULL, *pulse4 = NULL;

            pulse1 = (pulse *) work1;
            pulse1->off1 = pulse1->inc1 = pulse1->off3 = pulse1->inc3 = pulse1->off2 = 0;
            pulse1->inc2 = 0.0;
             /* First step is always the input frequency, so no adjust. */
            pulse1->carr_adj = pulse1->beat_adj = pulse1->phase_adj = pulse1->time_adj = pulse1->amp_adj = 0.0;
            pulse1->split_beat_adj = pulse1->split_adj = 0.0;
            /* Determine the step and slide frame sizes.  */
            int_64 slide_frames = (int_64) (out_rate * pulse1->slide_time);  // frames in each slide
            int_64 total_slide = (int_64) (slide_frames * pulse1->steps);  //  total slide frames
            int_64 step_frames = (snd1->tot_frames - total_slide) / pulse1->steps;  // frames in each step
            /*  Leftover frames after all step slides determined.  Add to last step. The total number
             *  of frames in the list has to be exactly the number of frames in the current time sequence. */
            int_64 frame_residue = (snd1->tot_frames - total_slide - (step_frames * pulse1->steps));
            pulse1->tot_frames = step_frames;
            pulse1->cur_frames = 0;  // pulse1 complete except for step list pointer set below.
            if (work2 != NULL)  // determine pulse we are step sliding to so steps and slides can be set up
            { 
              stub2 = (stub *) work2;
              if (stub2->type == 13 || stub2->type == 14 || stub2->type == 15)  // also pulse
                pulse2 = (pulse *) work2;
              else
                error ("Step slide called for, voice to slide to is not pulse.  Position matters!\n");
            } 
            else
              error ("Step slide called for, no next pulse in time sequence!\n");
            double carr_diff = (pulse2->carrier - pulse1->carrier);
            double beat_diff = (pulse2->beat - pulse1->beat);
            double phase_diff = (pulse2->phase - pulse1->phase);
            double time_diff = (pulse2->time - pulse1->time);
            double amp_diff = (pulse2->amp - pulse1->amp);
            double split_beat_diff = (pulse2->split_beat - pulse1->split_beat);
            int user_set_splits;  // Are the begin and end splits random or fixed?
            if (pulse1->split_begin == -1.0 || pulse1->split_end == -1.0)    // split start random or split end random
            {
              user_set_splits = 0;  // even if only 1 is random, treat as random for setup purposes
            }
            else  // both begin and end split are user specified
            {
              user_set_splits = 1;  // both begin and end splits specified by the user
              if (split_beat_diff != 0 || pulse1->split_beat > 0.0)  // there is a split beat or slide to split beat
              {
                if (pulse1->split_end < pulse1->split_begin)  // end always larger for split beat, swap if not
                {
                  double split_hold = pulse1->split_begin;  // swap begin and end
                  pulse1->split_begin = pulse1->split_end;
                  pulse1->split_end = split_hold;
                }
                /* Set split distance to the difference.  Not used for generating frames for pan, only split beat */
                pulse1->split_dist = pulse1->split_end - pulse1->split_begin;  
                double frames_per_cycle = ((double) out_rate / pulse1->split_beat);  // frames in a back and forth cycle
                  /* adjust to do that cycle, sign oscillates in generate_frames 
                   * Note that split_adj is being used differently than for pan, 
                   * There it is the adjustment to reach the end split over the course of the voice period.
                   * Here it is the adjustment so that the split oscillates between split_begin and split_end
                   * at the split_beat rate.  This works because the two are mutually exclusive. */
                pulse1->split_adj = ((2.*(pulse1->split_dist)) / frames_per_cycle);  
                pulse1->split_now = pulse1->split_begin;      // set working split to begin at
              }
              else  // there is a pan
              {
                  /* no split beat in this voice and not sliding to split beat in next voice, perform pan 
                   * Adjust per frame across all nodes at a constant rate so that arrive at end split at 
                   * end of list.
                   */
                pulse1->split_dist = 0.0;
                pulse1->split_adj = ((pulse1->split_end - pulse1->split_begin) / (double) snd1->tot_frames);
                pulse1->split_end = pulse1->split_begin + (pulse1->tot_frames * pulse1->split_adj);  // ending split
              }
            }
            /*  These are used to transfer the values at the end of a slide to the next step */
            double next_carrier = 0.0;
            double next_beat = 0.0;
            double next_phase = 0.0;
            double next_time = 0.0;
            double next_amp = 0.0;
            double next_split_beat = 0.0;
            pulse4 = pulse1;  // set last node processed
            int total_nodes = (2 * pulse1->steps);
            int ii;
            for (ii = 1; ii < total_nodes; ii++)  // create rest of step list nodes
            {
              pulse3 = (pulse *) Alloc ((sizeof (pulse)) * 1);  // create next node of step list
              if (ii % 2 == 1)  // a slide
              {
                memcpy ((void *) pulse3, (void *) pulse4, sizeof (pulse)); // copy last step
                pulse3->tot_frames = slide_frames;
                if (ii == total_nodes - 1)  // last slide, to next time sequence voice pulse2
                {
                  pulse2->last_off1 = &(pulse3->off1);
                  pulse2->last_off3 = &(pulse3->off3);
                  pulse2->last_off2 = &(pulse3->off2);
                  next_carrier = pulse2->carrier;
                  next_beat = pulse2->beat;
                  next_phase = pulse2->phase;
                  next_time = pulse2->time;
                  next_amp = pulse2->amp;
                  next_split_beat = pulse2->split_beat;
                  pulse3->step_next = NULL;  // last node, no next node
                }
                else  // internal slide
                {
                  double fraction = ((double) (ii+1)/(double) total_nodes);  // fraction of interval
                  next_carrier = pulse1->carrier + (carr_diff * fraction);
                  next_beat = pulse1->beat + (beat_diff * fraction);
                  next_phase = pulse1->phase + (phase_diff * fraction);
                  next_time = pulse1->time + (time_diff * fraction);
                  next_amp = pulse1->amp + (amp_diff * fraction);
                  next_split_beat = pulse1->split_beat + (split_beat_diff * fraction);
                  if (pulse1->fuzz > 0.0)  // fuzz the interval
                  {
                    double adjust = drand48() - 0.5;  // fuzz adjustment between -.5 and +.5 of fuzz
                    next_carrier += ((carr_diff/pulse1->steps) * pulse1->fuzz * adjust);
                    next_beat += ((beat_diff/pulse1->steps) * pulse1->fuzz * adjust);
                    next_phase += ((phase_diff/pulse1->steps) * pulse1->fuzz * adjust);
                    next_time += ((time_diff/pulse1->steps) * pulse1->fuzz * adjust);
                    next_amp += ((amp_diff/pulse1->steps) * pulse1->fuzz * adjust);
                    next_split_beat += ((split_beat_diff/pulse1->steps) * pulse1->fuzz * adjust);
                  }
                }
                pulse3->carr_adj = (next_carrier - pulse4->carrier)/ pulse3->tot_frames;
                pulse3->beat_adj = (next_beat - pulse4->beat)/ pulse3->tot_frames;
                pulse3->phase_adj = (next_phase - pulse4->phase)/ pulse3->tot_frames;
                pulse3->time_adj = (next_time - pulse4->time)/ pulse3->tot_frames;
                pulse3->amp_adj = (next_amp - pulse4->amp)/ pulse3->tot_frames;
                   /* change split beat only in slides */
                pulse3->split_beat_adj = (next_split_beat - pulse4->split_beat)/ pulse3->tot_frames;
              } 
              else  // a step
              {
                memcpy ((void *) pulse3, (void *) pulse1, sizeof (pulse)); // copy first in list to it
                if (ii == (total_nodes - 2))
                  pulse3->tot_frames += frame_residue;  // use up leftover frames in last step
                /* Set values used for calculation in last slide */
                pulse3->carrier = next_carrier;
                pulse3->beat = next_beat;
                pulse3->phase = next_phase;
                pulse3->time = next_time;
                pulse3->amp = next_amp;
                pulse3->split_beat = next_split_beat;
                pulse3->split_beat_adj = 0.0;  //steps are constant for split beat
              }
                /* Set up the random split logic here, the case where begin and end split specified
                 * taken care of above and housekeeping done for pan here.
                 * Use pulse1 to determine branching as it won't be changed until list is complete.
                 * Don't need to worry about overwriting begin and end splits as they are only used once
                 * Works like this:  
                 * If fixed begin split and end split with no split beat, pan occurs across all steps and 
                 * slides at a constant rate.  This was handled above.
                 * If fixed begin and end with split beat, the same begin and end are used for all nodes.
                 * This was handled above
                 * If random begin and/or end, then pan is a chain that runs through each voice node so
                 * that end in one node is begin in the next until the last.  Handled below.
                 * If it is random with a split beat, the begin and end are set anew in each node.  Handled below.
                 * Same logic for slides and steps
                 */
              if (! user_set_splits)  // at least one random split
              {
                if (split_beat_diff != 0 || pulse1->split_beat > 0.0)  // there is a split beat or slide to split beat
                {  /* Since split_begin and split_end don't change if there is a split
                    * beat, check if they are random and set them now.  If it is constant
                    * it has already been set by the memcpy above.
                    */
                  if (pulse1->split_begin == -1.0)  // pulse split start random
                  {
                     /* begin split is random */
                    double delta = ( (drand48 ()) * (pulse1->split_high - pulse1->split_low));
                    pulse3->split_begin = pulse1->split_low + delta;
                  }
                  if (pulse1->split_end == -1.0)  // pulse split end random
                  {
                    double delta = ( (drand48 ()) * (pulse1->split_high - pulse1->split_low));
                    pulse3->split_end = pulse1->split_low + delta; // end split for this pulse
                    while (fabs (pulse3->split_begin - pulse3->split_end) == 0.0)
                    {  // difference equal to zero?  Repeat until larger.  
                      delta = ( (drand48 ()) * (pulse1->split_high - pulse1->split_low));
                      pulse3->split_end = pulse1->split_low + delta;      // ending split for pulse
                    }
                  }
                  if (pulse3->split_end < pulse3->split_begin)  // end always larger for split beat, swap if not
                  {
                    double split_hold = pulse3->split_begin;  // swap begin and end
                    pulse3->split_begin = pulse3->split_end;
                    pulse3->split_end = split_hold;
                  }
                  pulse3->split_now = pulse3->split_begin;      // set working split to begin
                  pulse3->split_dist = pulse3->split_end - pulse3->split_begin;  // set split distance to the difference
                  double frames_per_cycle = ((double) out_rate / pulse3->split_beat);  // frames in a back and forth cycle
                    /* adjust to do that cycle, sign oscillates in generate_frames 
                     * Note that split_adj is being used differently than above, 
                     * There it is the adjustment to reach the end split over the course of the voice period.
                     * Here it is the adjustment so that the split oscillates between split_begin and split_end
                     * at the split_beat rate.  This works because the two are mutually exclusive. */
                  pulse3->split_adj = ((2.*(pulse3->split_dist)) / frames_per_cycle);  
                }
                else
                {
                  /* If it is a pan and split_begin or split_end are random, 
                   * change them for each voice node.
                   * If they aren't random, they are already set by the memcpy above.
                   */
                  if (pulse1->split_begin == -1.0)  // pulse split start random for pan
                  {
                    if (pulse4 != pulse1 && pulse1->split_end == -1.0)  
                        // previous node not first node in chain, pulse1 not set till end, both begin and end random
                      pulse3->split_begin = pulse4->split_end; // begin split is previous node end split
                    else  // first node after start of chain
                    {  /* begin split is random and will become first nodes end split below for pans */
                      double delta = ( (drand48 ()) * (pulse1->split_high - pulse1->split_low));
                      pulse3->split_begin = pulse1->split_low + delta;
                    }
                  }
                  pulse3->split_now = pulse3->split_begin;      // set working split to begin
                  if (pulse1->split_end == -1.0)  // pulse split end random for pan
                  {
                    if (ii == total_nodes - 1)  // last slide, to next time sequence voice pulse2
                    {
                      if (pulse2->split_begin == -1.0)  //random
                      {
                        double delta = ( (drand48 ()) * (pulse1->split_high - pulse1->split_low));
                        pulse3->split_end = pulse1->split_low + delta; // end split for this pulse
                        pulse2->split_begin = pulse3->split_end;  // set this as begin split for next voice
                      }
                      else  // fixed split in next voice
                        pulse3->split_end = pulse2->split_begin; // ending split is next voice begin split
                    }
                    else  // internal 
                    {
                      double delta = ( (drand48 ()) * (pulse1->split_high - pulse1->split_low));
                      pulse3->split_end = pulse1->split_low + delta;      // ending split for pulse
                    }
                  }
                  pulse3->split_dist = 0.0;  // set split distance to 0.0 for a pan, unused in generate frames
                    /* no split beat in this voice and not sliding to split beat in next voice, perform pan */
                  pulse3->split_adj = ((pulse3->split_end - pulse3->split_begin) 
                                                          / (double) pulse3->tot_frames);  // adjust per frame
                }
              }
              /* have to take care of pan across nodes here, so that each node starts at end of previous. */
              else if (split_beat_diff == 0.0 && pulse1->split_beat == 0.0)  // there is no split beat or slide to split beat
              {
                pulse3->split_begin =  pulse4->split_end + pulse4->split_adj;  // starting split for this node
                pulse3->split_end =  pulse3->split_begin + (pulse3->tot_frames * pulse3->split_adj);  // ending split
                pulse3->split_now = pulse3->split_begin;  // set working split to beginning split so adjust takes to end
              }
              pulse4->step_next = pulse3;  // set list pointer of previous node for next node in list to current node
              pulse3->last_off1 = &(pulse4->off1);  // each node starts where last left off as offset into sin table
              pulse3->last_off3 = &(pulse4->off3);  // each node starts where last left off as offset into sin table
              pulse3->last_off2 = &(pulse4->off2);  // each node starts where last left off as offset into sin table
              pulse4 = pulse3;  // make current node previous node
            }
              /* Now set up the split logic for pulse1 as it applies throughout the voice period.
                 Don't need to worry about overwriting begin and end splits as they are only used once
                 and the rest of the step slide list is done now so we don't need them as flags */
            if (! user_set_splits)  // at least one random split
            {
              if (split_beat_diff != 0 || pulse1->split_beat > 0.0)  // there is a split beat or slide to split beat
              {  /* Since split_begin and split_end don't change if there is a split
                  * beat, check if they are random and set them now.  If it is constant
                  * it has already been set by the setup above.
                  */
                if (pulse1->split_begin == -1.0)  // pulse split start random
                {
                   /* begin split is random */
                  double delta = ( (drand48 ()) * (pulse1->split_high - pulse1->split_low));
                  pulse1->split_begin = pulse1->split_low + delta;
                }
                if (pulse1->split_end == -1.0)  // pulse split end random
                {
                  double delta = ( (drand48 ()) * (pulse1->split_high - pulse1->split_low));
                  pulse1->split_end = pulse1->split_low + delta; // end split for this pulse
                  while (fabs (pulse1->split_begin - pulse1->split_end) == 0.0)
                  {  // difference equal to zero?  Repeat until larger.  
                    delta = ( (drand48 ()) * (pulse1->split_high - pulse1->split_low));
                    pulse1->split_end = pulse1->split_low + delta;      // ending split for pulse
                  }
                }
                if (pulse1->split_end < pulse1->split_begin)  // end always larger for split beat, swap if not
                {
                  double split_hold = pulse1->split_begin;  // swap begin and end
                  pulse1->split_begin = pulse1->split_end;
                  pulse1->split_end = split_hold;
                }
                pulse1->split_now = pulse1->split_begin;      // set working split to begin
                pulse1->split_dist = pulse1->split_end - pulse1->split_begin;  // set split distance to the difference
                double frames_per_cycle = ((double) out_rate / pulse1->split_beat);  // frames in a back and forth cycle
                  /* adjust to do that cycle, sign oscillates in generate_frames 
                   * Note that split_adj is being used differently than for pan, 
                   * There it is the adjustment to reach the end split over the course of the voice period.
                   * Here it is the adjustment so that the split oscillates between split_begin and split_end
                   * at the split_beat rate.  This works because the two are mutually exclusive. */
                pulse1->split_adj = ((2.*(pulse1->split_dist)) / frames_per_cycle);  
              }
              else
              {
                /* If it is a pan and split_begin or split_end are random, 
                 * change them for each voice node.
                 * If they aren't random, they are already set by the memcpy above.
                 */
                if (pulse1->split_end == -1.0)  // pulse split end random for pan
                {
                  if (pulse1->split_begin == -1.0)  // if both random, set end to next step node begin 
                    pulse1->split_end = (pulse1->step_next)->split_begin;
                  else
                  { /* begin split is fixed  */
                    double delta = ( (drand48 ()) * (pulse1->split_high - pulse1->split_low));
                    pulse1->split_end = pulse1->split_low + delta;      // ending split for pulse
                  }
                }
                if (pulse1->split_begin == -1.0)  // pulse split start random for pan
                {
                  double delta = ( (drand48 ()) * (pulse1->split_high - pulse1->split_low));
                  pulse1->split_begin = pulse1->split_low + delta;
                }
                pulse1->split_now = pulse1->split_begin;      // set working split to begin
                pulse1->split_dist = 0.0;  // set split distance to 0.0 for a pan, unused in generate frames
                  /* no split beat in this voice and not sliding to split beat in next voice, perform pan */
                pulse1->split_adj = ((pulse1->split_end - pulse1->split_begin) 
                                                        / (double) pulse1->tot_frames);  // adjust per frame
              }
            }
            /* have to take care of pan across nodes here, so that each node starts at end of previous. */
            else if (split_beat_diff == 0.0 && pulse1->split_beat == 0.0)  // there is no split beat or slide to split beat
            {
              /* split_begin and split_end already set above, no need to modify here */
              pulse1->split_now = pulse1->split_begin;  // set working split to beginning split so adjust takes to end
            }
            break;
          }
        case 15:  // pulse vary slide, have to create list of steps and slides
          { 
            pulse *pulse1 = NULL, *pulse2 = NULL, *pulse3 = NULL, *pulse4 = NULL;

            pulse1 = (pulse *) work1;
            pulse1->off1 = pulse1->inc1 = pulse1->off3 = pulse1->inc3 = pulse1->off2 = 0;
            pulse1->inc2 = 0.0;
             /* First step is always the input frequency, so no adjust. */
            pulse1->carr_adj = pulse1->beat_adj = pulse1->phase_adj = pulse1->time_adj = pulse1->amp_adj = 0.0;
            pulse1->split_beat_adj = pulse1->split_adj = 0.0;
            /* Determine the step and slide frame sizes.  */
            int_64 slide_frames = (int_64) (out_rate * pulse1->slide_time);  // frames in each slide
            int_64 total_slide = (int_64) (slide_frames * pulse1->steps);  //  total slide frames
            int_64 step_frames = (snd1->tot_frames - total_slide) / pulse1->steps;  // frames in each step
            /*  Leftover frames after all step slides determined.  Add to last slide. The total number
             *  of frames in the list has to be exactly the number of frames in the current time sequence. */
            int_64 frame_residue = (snd1->tot_frames - total_slide - (step_frames * pulse1->steps));
            pulse1->tot_frames = step_frames;
            pulse1->cur_frames = 0;  // pulse1 complete except for step list pointer set below.
            if (work2 != NULL)  // determine pulse we are step sliding to so steps and slides can be set up
            { 
              stub2 = (stub *) work2;
              if (stub2->type == 13 || stub2->type == 14 || stub2->type == 15)  // also pulse
                pulse2 = (pulse *) work2;
              else
                error ("Vary slide called for, voice to slide to is not pulse.  Position matters!\n");
            } 
            else
              error ("Vary slide called for, no next pulse in time sequence!\n");
            double carr_diff = (pulse2->carrier - pulse1->carrier);
            double beat_diff = (pulse2->beat - pulse1->beat);
            double phase_diff = (pulse2->phase - pulse1->phase);
            double time_diff = (pulse2->time - pulse1->time);
            double amp_diff = (pulse2->amp - pulse1->amp);
            double split_beat_diff = (pulse2->split_beat - pulse1->split_beat);
            int user_set_splits;  // Are the begin and end splits random or fixed?
            if (pulse1->split_begin == -1.0 || pulse1->split_end == -1.0)    // split start random or split end random
            {
              user_set_splits = 0;  // even if only 1 is random, treat as random for setup purposes
            }
            else  // both begin and end split are user specified
            {
              user_set_splits = 1;  // both begin and end splits specified by the user
              if (split_beat_diff != 0.0 || pulse1->split_beat > 0.0)  // there is a split beat or slide to split beat
              {
                if (pulse1->split_end < pulse1->split_begin)  // end always larger for split beat, swap if not
                {
                  double split_hold = pulse1->split_begin;  // swap begin and end
                  pulse1->split_begin = pulse1->split_end;
                  pulse1->split_end = split_hold;
                }
                /* Set split distance to the difference.  Not used for generating frames for pan, only split beat */
                pulse1->split_dist = pulse1->split_end - pulse1->split_begin;  
                double frames_per_cycle = ((double) out_rate / pulse1->split_beat);  // frames in a back and forth cycle
                  /* adjust to do that cycle, sign oscillates in generate_frames 
                   * Note that split_adj is being used differently than for pan, 
                   * There it is the adjustment to reach the end split over the course of the voice period.
                   * Here it is the adjustment so that the split oscillates between split_begin and split_end
                   * at the split_beat rate.  This works because the two are mutually exclusive. */
                pulse1->split_adj = ((2.*(pulse1->split_dist)) / frames_per_cycle);  
                pulse1->split_now = pulse1->split_begin;      // set working split to begin
              }
              else  // there is a pan
              {
                  /* no split beat in this voice and not sliding to split beat in next voice, perform pan 
                   * Adjust per frame across all nodes at a constant rate so that arrive at end split at 
                   * end of list.
                   */
                pulse1->split_dist = 0.0;
                pulse1->split_adj = ((pulse1->split_end - pulse1->split_begin) / (double) snd1->tot_frames);
                pulse1->split_end = pulse1->split_begin + (pulse1->tot_frames * pulse1->split_adj);  // ending split
              }
            }
            /*  These are used to transfer the values at the end of a slide to the next step */
            double next_carrier = 0.0;
            double next_beat = 0.0;
            double next_phase = 0.0;
            double next_time = 0.0;
            double next_amp = 0.0;
            double next_split_beat = 0.0;
            pulse4 = pulse1;  // set last node processed
            int total_nodes = (2 * pulse1->steps);
            int ii;
            for (ii = 1; ii < total_nodes; ii++)  // create rest of step list nodes
            {
              pulse3 = (pulse *) Alloc ((sizeof (pulse)) * 1);  // create next node of step list
              if (ii % 2 == 1)  // a slide
              {
                memcpy ((void *) pulse3, (void *) pulse4, sizeof (pulse)); // copy last step
                pulse3->tot_frames = slide_frames;
                if (ii == total_nodes - 1)  // last slide, to next time sequence voice pulse2
                {
                  pulse2->last_off1 = &(pulse3->off1);
                  pulse2->last_off3 = &(pulse3->off3);
                  pulse2->last_off2 = &(pulse3->off2);
                  next_carrier = pulse2->carrier;
                  next_beat = pulse2->beat;
                  next_phase = pulse2->phase;
                  next_time = pulse2->time;
                  next_amp = pulse2->amp;
                  next_split_beat = pulse2->split_beat;
                  pulse3->step_next = NULL;  // last node, no next node
                }
                else  // internal slide
                {
                  double fraction = drand48 ();  // random fraction of interval
                  next_carrier = pulse1->carrier + (carr_diff * fraction);
                  fraction = drand48 ();  // random fraction of interval
                  next_beat = pulse1->beat + (beat_diff * fraction);
                  fraction = drand48 ();  // random fraction of interval
                  next_phase = pulse1->phase + (phase_diff * fraction);
                  fraction = drand48 ();  // random fraction of interval
                  next_time = pulse1->time + (time_diff * fraction);
                  fraction = drand48 ();  // random fraction of interval
                  next_amp = pulse1->amp + (amp_diff * fraction);
                  fraction = drand48 ();  // random fraction of interval
                  next_split_beat = pulse1->split_beat + (split_beat_diff * fraction);
                }
                pulse3->carr_adj = (next_carrier - pulse4->carrier)/ pulse3->tot_frames;
                pulse3->beat_adj = (next_beat - pulse4->beat)/ pulse3->tot_frames;
                pulse3->phase_adj = (next_phase - pulse4->phase)/ pulse3->tot_frames;
                pulse3->time_adj = (next_time - pulse4->time)/ pulse3->tot_frames;
                pulse3->amp_adj = (next_amp - pulse4->amp)/ pulse3->tot_frames;
                   /* change split beat only in slides */
                pulse3->split_beat_adj = (next_split_beat - pulse4->split_beat)/ pulse3->tot_frames;
              } 
              else  // a step
              {
                memcpy ((void *) pulse3, (void *) pulse1, sizeof (pulse)); // copy first in list to it
                if (ii == (total_nodes - 2))
                  pulse3->tot_frames += frame_residue;  // use up leftover frames in last step
                /* Set values used for calculation in last slide */
                pulse3->carrier = next_carrier;
                pulse3->beat = next_beat;
                pulse3->phase = next_phase;
                pulse3->time = next_time;
                pulse3->amp = next_amp;
                pulse3->split_beat = next_split_beat;
                pulse3->split_beat_adj = 0.0;  //steps are constant
              }
                /* Set up the random split logic here, the case where begin and end split specified
                 * taken care of above and housekeeping done for pan here.
                 * Use pulse1 to determine branching as it won't be changed until list is complete.
                 * Don't need to worry about overwriting begin and end splits as they are only used once
                 * Works like this:  
                 * If fixed begin split and end split with no split beat, pan occurs across all steps and 
                 * slides at a constant rate.  This was handled above.
                 * If fixed begin and end with split beat, the same begin and end are used for all nodes.
                 * This was handled above
                 * If random begin and/or end, then pan is a chain that runs through each voice node so
                 * that end in one node is begin in the next until the last.  Handled below.
                 * If it is random with a split beat, the begin and end are set anew in each node.  Handled below.
                 * Same logic for slides and steps
                 */
              if (! user_set_splits)  // at least one random split
              {
                if (split_beat_diff != 0 || pulse1->split_beat > 0.0)  // there is a split beat or slide to split beat
                {  /* Since split_begin and split_end don't change if there is a split
                    * beat, check if they are random and set them now.  If it is constant
                    * it has already been set by the memcpy above.
                    */
                  if (pulse1->split_begin == -1.0)  // pulse split start random
                  {
                     /* begin split is random */
                    double delta = ( (drand48 ()) * (pulse1->split_high - pulse1->split_low));
                    pulse3->split_begin = pulse1->split_low + delta;
                  }
                  if (pulse1->split_end == -1.0)  // pulse split end random
                  {
                    double delta = ( (drand48 ()) * (pulse1->split_high - pulse1->split_low));
                    pulse3->split_end = pulse1->split_low + delta; // end split for this pulse
                    while (fabs (pulse3->split_begin - pulse3->split_end) == 0.0)
                    {  // difference equal to zero?  Repeat until larger.  
                      delta = ( (drand48 ()) * (pulse1->split_high - pulse1->split_low));
                      pulse3->split_end = pulse1->split_low + delta;      // ending split for pulse
                    }
                  }
                  if (pulse3->split_end < pulse3->split_begin)  // end always larger for split beat, swap if not
                  {
                    double split_hold = pulse3->split_begin;  // swap begin and end
                    pulse3->split_begin = pulse3->split_end;
                    pulse3->split_end = split_hold;
                  }
                  pulse3->split_now = pulse3->split_begin;      // set working split to begin
                  pulse3->split_dist = pulse3->split_end - pulse3->split_begin;  // set split distance to the difference
                  double frames_per_cycle = ((double) out_rate / pulse3->split_beat);  // frames in a back and forth cycle
                    /* adjust to do that cycle, sign oscillates in generate_frames 
                     * Note that split_adj is being used differently than for pan.
                     * There it is the adjustment to reach the end split over the course of the voice period.
                     * Here it is the adjustment so that the split oscillates between split_begin and split_end
                     * at the split_beat rate.  This works because the two are mutually exclusive. */
                  pulse3->split_adj = ((2.*(pulse3->split_dist)) / frames_per_cycle);  
                }
                else
                {
                  /* If it is a pan and split_begin or split_end are random, 
                   * change them for each voice node.
                   * If they aren't random, they are already set by the memcpy above.
                   */
                  if (pulse1->split_begin == -1.0)  // pulse split start random for pan
                  {
                     /* begin split is random */
                    double delta = ( (drand48 ()) * (pulse1->split_high - pulse1->split_low));
                    pulse3->split_begin = pulse1->split_low + delta;
                  }
                  pulse3->split_now = pulse3->split_begin;      // set working split to begin
                  if (pulse1->split_end == -1.0)  // pulse split end random for pan
                  {
                    if (ii == total_nodes - 1)  // last slide, to next time sequence voice pulse2
                    {
                      if (pulse2->split_begin == -1.0)  //random
                      {
                        double delta = ( (drand48 ()) * (pulse1->split_high - pulse1->split_low));
                        pulse3->split_end = pulse1->split_low + delta; // end split for this pulse
                        pulse2->split_begin = pulse3->split_end;  // set this as begin split for next voice
                      }
                      else  // fixed split in next voice
                        pulse3->split_end = pulse2->split_begin; // ending split is next voice begin split
                    }
                    else  // internal 
                    {
                      double delta = ( (drand48 ()) * (pulse1->split_high - pulse1->split_low));
                      pulse3->split_end = pulse1->split_low + delta;      // ending split for pulse
                    }
                  }
                  pulse3->split_dist = 0.0;  // set split distance to 0.0 for a pan, unused in generate frames
                    /* no split beat in this voice and not sliding to split beat in next voice, perform pan */
                  pulse3->split_adj = ((pulse3->split_end - pulse3->split_begin) 
                                                          / (double) pulse3->tot_frames);  // adjust per frame
                }
              }
              /* have to take care of pan across nodes here, so that each node starts at end of previous. */
              else if (split_beat_diff == 0.0 && pulse1->split_beat == 0.0)  // there is no split beat or slide to split beat
              {
                pulse3->split_begin =  pulse4->split_end + pulse4->split_adj;  // starting split for this node
                pulse3->split_end =  pulse3->split_begin + (pulse3->tot_frames * pulse3->split_adj);  // ending split
                pulse3->split_now = pulse3->split_begin;  // set working split to beginning split so adjust takes to end
              }
              pulse4->step_next = pulse3;  // set list pointer of previous node for next node in list to current node
              pulse3->last_off1 = &(pulse4->off1);  // each node starts where last left off as offset into sin table
              pulse3->last_off3 = &(pulse4->off3);  // each node starts where last left off as offset into sin table
              pulse3->last_off2 = &(pulse4->off2);  // each node starts where last left off as offset into sin table
              pulse4 = pulse3;  // make current node previous node
            }
              /* Now set up the split logic for pulse1 as it applies throughout the voice period.
                 Don't need to worry about overwriting begin and end splits as they are only used once
                 and the rest of the step slide list is done */
            if (! user_set_splits)  // at least one random split
            {
              if (split_beat_diff != 0 || pulse1->split_beat > 0.0)  // there is a split beat or slide to split beat
              {  /* Since split_begin and split_end don't change if there is a split
                  * beat, check if they are random and set them now.  If it is constant
                  * it has already been set by the setup above.
                  */
                if (pulse1->split_begin == -1.0)  // pulse split start random
                {
                   /* begin split is random */
                  double delta = ( (drand48 ()) * (pulse1->split_high - pulse1->split_low));
                  pulse1->split_begin = pulse1->split_low + delta;
                }
                if (pulse1->split_end == -1.0)  // pulse split end random
                {
                  double delta = ( (drand48 ()) * (pulse1->split_high - pulse1->split_low));
                  pulse1->split_end = pulse1->split_low + delta; // end split for this pulse
                  while (fabs (pulse1->split_begin - pulse1->split_end) == 0.0)
                  {  // difference equal to zero?  Repeat until larger.  
                    delta = ( (drand48 ()) * (pulse1->split_high - pulse1->split_low));
                    pulse1->split_end = pulse1->split_low + delta;      // ending split for pulse
                  }
                }
                if (pulse1->split_end < pulse1->split_begin)  // end always larger for split beat, swap if not
                {
                  double split_hold = pulse1->split_begin;  // swap begin and end
                  pulse1->split_begin = pulse1->split_end;
                  pulse1->split_end = split_hold;
                }
                pulse1->split_now = pulse1->split_begin;      // set working split to begin
                pulse1->split_dist = pulse1->split_end - pulse1->split_begin;  // set split distance to the difference
                double frames_per_cycle = ((double) out_rate / pulse1->split_beat);  // frames in a back and forth cycle
                  /* adjust to do that cycle, sign oscillates in generate_frames 
                   * Note that split_adj is being used differently than above, 
                   * There it is the adjustment to reach the end split over the course of the voice period.
                   * Here it is the adjustment so that the split oscillates between split_begin and split_end
                   * at the split_beat rate.  This works because the two are mutually exclusive. */
                pulse1->split_adj = ((2.*(pulse1->split_dist)) / frames_per_cycle);  
              }
              else
              {
                /* If it is a pan and split_begin or split_end are random, 
                 * change them for each voice node.
                 * If they aren't random, they are already set by the memcpy above.
                 */
                if (pulse1->split_begin == -1.0)  // pulse split start random for pan
                {
                  /* begin split is random and will become first nodes end split below for pans */
                  double delta = ( (drand48 ()) * (pulse1->split_high - pulse1->split_low));
                  pulse1->split_begin = pulse1->split_low + delta;
                }
                if (pulse1->split_end == -1.0)  // pulse split end random for pan
                {
                  double delta = ( (drand48 ()) * (pulse1->split_high - pulse1->split_low));
                  pulse1->split_end = pulse1->split_low + delta;      // ending split for pulse
                }
                pulse1->split_now = pulse1->split_begin;      // set working split to begin
                pulse1->split_dist = 0.0;  // set split distance to 0.0 for a pan, unused in generate frames
                  /* no split beat in this voice and not sliding to split beat in next voice, perform pan */
                pulse1->split_adj = ((pulse1->split_end - pulse1->split_begin) 
                                                        / (double) pulse1->tot_frames);  // adjust per frame
              }
            }
            /* have to take care of pan across nodes here, so that each node starts at end of previous. */
            else if (split_beat_diff == 0.0 && pulse1->split_beat == 0.0)  // there is no split beat or slide to split beat
            {
              /* split_begin and split_end already set above, no need to modify here */
              pulse1->split_now = pulse1->split_begin;  // set working split to beginning split so adjust takes to end
            }
            break;
          }
        case 16:  // phase
          { 
            phase *phase1 = NULL, *phase2 = NULL;

            phase1 = (phase *) work1;
            phase1->off1 = phase1->inc1 = 0;
            phase1->amp_off1 = phase1->amp_inc1 = phase1->amp_off2 = phase1->amp_inc2 = 0;
            if (work2 != NULL)
            { 
              stub2 = (stub *) work2;
              if (stub2->type == 16 || stub2->type == 17 || stub2->type == 18)  // also phase
              { 
                phase2 = (phase *) work2;
                /* Set the pointers to the previous voice's offsets here so it can be used while running.
                   Need to do this even when there is no slide.  Some duplication with below. */
                phase2->last_off1 = &(phase1->off1);
                phase2->last_amp_off1 = &(phase1->amp_off1);
                phase2->last_amp_off2 = &(phase1->amp_off2);
                phase2->last_shift = &(phase1->shift);
                phase2->last_direction = &(phase1->direction);
              } 
            } 
            if (phase1->slide == 0)
            { 
              phase1->carr_adj = phase1->beat_adj = phase1->amp_adj = phase1->phase_adj = 0.0;
              phase1->amp_beat1_adj = phase1->amp_beat2_adj = 0.0;
              phase1->amp_pct1_adj = phase1->amp_pct2_adj = 0.0;
            } 
            else  // slide to next phase in stream
            { 
              if (work2 != NULL)
              { 
                if (phase2 != NULL)  // set above if phase, NULL means next voice not phase
                {
                  phase1->carr_adj = (phase2->carrier - phase1->carrier)/ (double) snd1->tot_frames;
                  phase1->beat_adj = (phase2->beat - phase1->beat)/ (double) snd1->tot_frames;
                  phase1->amp_adj = (phase2->amp - phase1->amp)/ (double) snd1->tot_frames;
                  phase1->phase_adj = (phase2->phase - phase1->phase)/ (double) snd1->tot_frames;
                  /* Amplitude beats are optional.  If there isn't a match, treat as zero instead */
                  if (phase2->amp_beat1 > 0.0)
                    phase1->amp_beat1_adj = (phase2->amp_beat1 - phase1->amp_beat1)/ (double) snd1->tot_frames;
                  else  // zero amp_beat1 in next phase
                    phase1->amp_beat1_adj = - phase1->amp_beat1 / (double) snd1->tot_frames;
                  if (phase2->amp_beat2 > 0.0)
                    phase1->amp_beat2_adj = (phase2->amp_beat2 - phase1->amp_beat2)/ (double) snd1->tot_frames;
                  else  // zero amp_beat2 in next phase
                    phase1->amp_beat2_adj = - phase1->amp_beat2 / (double) snd1->tot_frames;
                  /* Amplitude percents are optional.  If there isn't a match, treat as zero instead */
                  if (phase2->amp_pct1 > 0.0)
                    phase1->amp_pct1_adj = (phase2->amp_pct1 - phase1->amp_pct1)/ (double) snd1->tot_frames;
                  else  // zero amp_pct1 in next phase
                    phase1->amp_pct1_adj = - phase1->amp_pct1 / (double) snd1->tot_frames;
                  if (phase2->amp_pct2 > 0.0)
                    phase1->amp_pct2_adj = (phase2->amp_pct2 - phase1->amp_pct2)/ (double) snd1->tot_frames;
                  else  // zero amp_pct2 in next phase
                    phase1->amp_pct2_adj = - phase1->amp_pct2 / (double) snd1->tot_frames;
                } 
                else
                  error ("Slide called for, voice to slide to is not phase.  Position matters!\n");
              } 
              else
                error ("Slide called for, no next phase in time sequence!\n");
            }
            break;
          }
        case 17:  // phase step slide, have to create list of steps and slides
          { 
            phase *phase1 = NULL, *phase2 = NULL, *phase3 = NULL, *phase4 = NULL;

            phase1 = (phase *) work1;
            phase1->off1 = phase1->inc1 = 0;
            phase1->amp_off1 = phase1->amp_inc1 = phase1->amp_off2 = phase1->amp_inc2 = 0;
             /* First step is always the input frequency, so no adjust. */
            phase1->carr_adj = phase1->beat_adj = phase1->amp_adj = phase1->phase_adj = 0.0;
            phase1->amp_beat1_adj = phase1->amp_beat2_adj = 0.0;
            phase1->amp_pct1_adj = phase1->amp_pct2_adj = 0.0;
            /* Determine the step and slide frame sizes.  */
            int_64 slide_frames = (int_64) (out_rate * phase1->slide_time);  // frames in each slide
            int_64 total_slide = (int_64) (slide_frames * phase1->steps);  //  total slide time
            int_64 step_frames = (snd1->tot_frames - total_slide) / phase1->steps;  // frames in each step
            /*  Leftover frames after all step slides determined.  Add to last step. The total number
             *  of frames in the list has to be exactly the number of frames in the current time sequence. */
            int_64 frame_residue = (snd1->tot_frames - total_slide - (step_frames * phase1->steps));
            phase1->tot_frames = step_frames;
            phase1->cur_frames = 0;  // phase1 complete except for step list pointer set below.
            if (work2 != NULL)  // determine phase we are step sliding to so steps and slides can be set up
            { 
              stub2 = (stub *) work2;
              if (stub2->type == 16 || stub2->type == 17 || stub2->type == 18)  // also phase
                phase2 = (phase *) work2;
              else
                error ("Step slide called for, voice to slide to is not phase.  Position matters!\n");
            } 
            else
              error ("Step slide called for, no next phase in time sequence!\n");
            double carr_diff = (phase2->carrier - phase1->carrier);
            double beat_diff = (phase2->beat - phase1->beat);
            double amp_diff = (phase2->amp - phase1->amp);
            double phase_diff = (phase2->phase - phase1->phase);
            double amp_beat1_diff = (phase2->amp_beat1 - phase1->amp_beat1);
            double amp_beat2_diff = (phase2->amp_beat2 - phase1->amp_beat2);
            double amp_pct1_diff = (phase2->amp_pct1 - phase1->amp_pct1);
            double amp_pct2_diff = (phase2->amp_pct2 - phase1->amp_pct2);
            double next_carrier = 0.0;
            double next_beat = 0.0;
            double next_amp = 0.0;
            double next_phase = 0.0;
            double next_amp_beat1 = 0.0;
            double next_amp_beat2 = 0.0;
            double next_amp_pct1 = 0.0;
            double next_amp_pct2 = 0.0;
            phase4 = phase1;  // set last node processed
            int total_nodes = (2 * phase1->steps);
            int ii;
            for (ii = 1; ii < total_nodes; ii++)  // create rest of step list nodes
            {
              phase3 = (phase *) Alloc ((sizeof (phase)) * 1);  // create next node of step list
              if (ii % 2 == 1)  // a slide
              {
                memcpy ((void *) phase3, (void *) phase4, sizeof (phase)); // copy last step
                phase3->tot_frames = slide_frames;
                if (ii == total_nodes - 1)  // last slide, to next time sequence voice phase2
                {
                  phase2->last_off1 = &(phase3->off1);
                  phase2->last_amp_off1 = &(phase3->amp_off1);
                  phase2->last_amp_off2 = &(phase3->amp_off2);
                  phase2->last_shift = &(phase3->shift);
                  phase2->last_direction = &(phase3->direction);
                  next_carrier = phase2->carrier;
                  next_beat = phase2->beat;
                  next_amp = phase2->amp;
                  next_phase = phase2->phase;
                  next_amp_beat1 = phase2->amp_beat1;
                  next_amp_beat2 = phase2->amp_beat2;
                  next_amp_pct1 = phase2->amp_pct1;
                  next_amp_pct2 = phase2->amp_pct2;
                  phase3->step_next = NULL;  // last node, no next node
                }
                else  // internal slide
                {
                  double fraction = ((double) (ii+1)/(double) total_nodes);  // fraction of interval
                  next_carrier = phase1->carrier + (carr_diff * fraction);
                  next_beat = phase1->beat + (beat_diff * fraction);
                  next_amp = phase1->amp + (amp_diff * fraction);
                  next_phase = phase1->phase + (phase_diff * fraction);
                  next_amp_beat1 = phase1->amp_beat1 + (amp_beat1_diff * fraction);
                  next_amp_beat2 = phase1->amp_beat2 + (amp_beat2_diff * fraction);
                  next_amp_pct1 = phase1->amp_pct1 + (amp_pct1_diff * fraction);
                  next_amp_pct2 = phase1->amp_pct2 + (amp_pct2_diff * fraction);
                  if (phase1->fuzz > 0.0)  // fuzz the interval
                  {
                    double adjust = drand48() - 0.5;  // fuzz adjustment between -.5 and +.5 of fuzz
                    next_carrier += ((carr_diff/phase1->steps) * phase1->fuzz * adjust);
                    next_beat += ((beat_diff/phase1->steps) * phase1->fuzz * adjust);
                    next_amp += ((amp_diff/phase1->steps) * phase1->fuzz * adjust);
                    next_phase += ((phase_diff/phase1->steps) * phase1->fuzz * adjust);
                    next_amp_beat1 += ((amp_beat1_diff/phase1->steps) * phase1->fuzz * adjust);
                    next_amp_beat2 += ((amp_beat2_diff/phase1->steps) * phase1->fuzz * adjust);
                    next_amp_pct1 += ((amp_pct1_diff/phase1->steps) * phase1->fuzz * adjust);
                    next_amp_pct2 += ((amp_pct2_diff/phase1->steps) * phase1->fuzz * adjust);
                  }
                }
                phase3->carr_adj = (next_carrier - phase4->carrier)/ phase3->tot_frames;
                phase3->beat_adj = (next_beat - phase4->beat)/ phase3->tot_frames;
                phase3->amp_adj = (next_amp - phase4->amp)/ phase3->tot_frames;
                phase3->phase_adj = (next_phase - phase4->phase)/ phase3->tot_frames;
                /* Amplitude beats are optional.  If there isn't a match, treat as zero instead */
                if (next_amp_beat1 > 0.0)
                  phase3->amp_beat1_adj = (next_amp_beat1 - phase4->amp_beat1)/ phase3->tot_frames;
                else  // zero amp_beat1 in next phase
                  phase3->amp_beat1_adj = - phase4->amp_beat1 / phase3->tot_frames;
                if (next_amp_beat2 > 0.0)
                  phase3->amp_beat2_adj = (next_amp_beat2 - phase4->amp_beat2)/ phase3->tot_frames;
                else  // zero amp_beat2 in next phase
                  phase3->amp_beat2_adj = - phase4->amp_beat2 / phase3->tot_frames;
                /* Amplitude percents are optional.  If there isn't a match, treat as zero instead */
                if (next_amp_pct1 > 0.0)
                  phase3->amp_pct1_adj = (next_amp_pct1 - phase4->amp_pct1)/ phase3->tot_frames;
                else  // zero amp_pct1 in next phase
                  phase3->amp_pct1_adj = - phase4->amp_pct1 / phase3->tot_frames;
                if (next_amp_pct2 > 0.0)
                  phase3->amp_pct2_adj = (next_amp_pct2 - phase4->amp_pct2)/ phase3->tot_frames;
                else  // zero amp_pct2 in next phase
                  phase3->amp_pct2_adj = - phase4->amp_pct2 / phase3->tot_frames;
              } 
              else  // a step
              {
                memcpy ((void *) phase3, (void *) phase1, sizeof (phase)); // copy first in list to it
                if (ii == (total_nodes - 2))
                  phase3->tot_frames += frame_residue;  // use up leftover frames in last step
                /* Set values used for calculation in last slide */
                phase3->carrier = next_carrier;
                phase3->beat = next_beat;
                phase3->amp = next_amp;
                phase3->phase = next_phase;
                phase3->amp_beat1 = next_amp_beat1;
                phase3->amp_beat2 = next_amp_beat2;
                phase3->amp_pct1 = next_amp_pct1;
                phase3->amp_pct2 = next_amp_pct2;
              }
              phase4->step_next = phase3;  // set list pointer for previous node
              phase3->last_off1 = &(phase4->off1);  // each node starts where last left off as offset
              phase3->last_amp_off1 = &(phase4->amp_off1);  // each node starts where last left off as amp_offset
              phase3->last_amp_off2 = &(phase4->amp_off2);
              phase3->last_shift = &(phase4->shift);  // each node starts where last left off for phase and direction
              phase3->last_direction = &(phase4->direction);
              phase4 = phase3;  // make current node previous node
            }
            break;
          }
        case 18:  // phase vary slide, have to create list of steps and slides
          { 
            phase *phase1 = NULL, *phase2 = NULL, *phase3 = NULL, *phase4 = NULL;

            phase1 = (phase *) work1;
            phase1->off1 = phase1->inc1 = 0;
            phase1->amp_off1 = phase1->amp_inc1 = phase1->amp_off2 = phase1->amp_inc2 = 0;
             /* First step is always the input frequency, so no adjust. */
            phase1->carr_adj = phase1->beat_adj = phase1->amp_adj = phase1->phase_adj = 0.0;
            phase1->amp_beat1_adj = phase1->amp_beat2_adj = 0.0;
            phase1->amp_pct1_adj = phase1->amp_pct2_adj = 0.0;
            /* Determine the step and slide frame sizes.  */
            int_64 slide_frames = (int_64) (out_rate * phase1->slide_time);  // frames in each slide
            int_64 total_slide = (int_64) (slide_frames * phase1->steps);  //  total slide time
            int_64 step_frames = (snd1->tot_frames - total_slide) / phase1->steps;  // frames in each step
            /*  Leftover frames after all step slides determined.  Add to last slide. The total number
             *  of frames in the list has to be exactly the number of frames in the current time sequence. */
            int_64 frame_residue = (snd1->tot_frames - total_slide - (step_frames * phase1->steps));
            phase1->tot_frames = step_frames;
            phase1->cur_frames = 0;  // phase1 complete except for step list pointer set below.
            if (work2 != NULL)  // determine phase we are step sliding to so steps and slides can be set up
            { 
              stub2 = (stub *) work2;
              if (stub2->type == 16 || stub2->type == 17 || stub2->type == 18)  // also phase
                phase2 = (phase *) work2;
              else
                error ("Vary slide called for, voice to slide to is not phase.  Position matters!\n");
            } 
            else
              error ("Vary slide called for, no next phase in time sequence!\n");
            double carr_diff = (phase2->carrier - phase1->carrier);
            double beat_diff = (phase2->beat - phase1->beat);
            double amp_diff = (phase2->amp - phase1->amp);
            double phase_diff = (phase2->phase - phase1->phase);
            double amp_beat1_diff = (phase2->amp_beat1 - phase1->amp_beat1);
            double amp_beat2_diff = (phase2->amp_beat2 - phase1->amp_beat2);
            double amp_pct1_diff = (phase2->amp_pct1 - phase1->amp_pct1);
            double amp_pct2_diff = (phase2->amp_pct2 - phase1->amp_pct2);
            double next_carrier = 0.0;
            double next_beat = 0.0;
            double next_amp = 0.0;
            double next_phase = 0.0;
            double next_amp_beat1 = 0.0;
            double next_amp_beat2 = 0.0;
            double next_amp_pct1 = 0.0;
            double next_amp_pct2 = 0.0;
            phase4 = phase1;  // set last node processed
            int total_nodes = (2 * phase1->steps);
            int ii;
            for (ii = 1; ii < total_nodes; ii++)  // create rest of vary list nodes
            {
              phase3 = (phase *) Alloc ((sizeof (phase)) * 1);  // create next node of vary list
              if (ii % 2 == 1)  // a slide
              {
                memcpy ((void *) phase3, (void *) phase4, sizeof (phase)); // copy last step
                phase3->tot_frames = slide_frames;
                if (ii == total_nodes - 1)  // last slide, to next time sequence voice phase2
                {
                  phase2->last_off1 = &(phase3->off1);  // phase2 will start from these offsets
                  phase2->last_amp_off1 = &(phase3->amp_off1);  // phase2 will start from these amp_offsets
                  phase2->last_amp_off2 = &(phase3->amp_off2);
                  phase2->last_shift = &(phase3->shift);
                  phase2->last_direction = &(phase3->direction);
                  next_carrier = phase2->carrier;
                  next_beat = phase2->beat;
                  next_amp = phase2->amp;
                  next_phase = phase2->phase;
                  next_amp_beat1 = phase2->amp_beat1;
                  next_amp_beat2 = phase2->amp_beat2;
                  next_amp_pct1 = phase2->amp_pct1;
                  next_amp_pct2 = phase2->amp_pct2;
                  phase3->step_next = NULL;  // last node, no next node
                  phase3->tot_frames += frame_residue;  // use up leftover frames in last slide
                }
                else  // internal slide
                {
                  double fraction = drand48 ();  // random fraction of interval
                  next_carrier = phase1->carrier + (carr_diff * fraction);
                  next_beat = phase1->beat + (beat_diff * fraction);
                  next_amp = phase1->amp + (amp_diff * fraction);
                  next_phase = phase1->phase + (phase_diff * fraction);
                  next_amp_beat1 = phase1->amp_beat1 + (amp_beat1_diff * fraction);
                  next_amp_beat2 = phase1->amp_beat2 + (amp_beat2_diff * fraction);
                  next_amp_pct1 = phase1->amp_pct1 + (amp_pct1_diff * fraction);
                  next_amp_pct2 = phase1->amp_pct2 + (amp_pct2_diff * fraction);
                }
                phase3->carr_adj = (next_carrier - phase4->carrier)/ phase3->tot_frames;
                phase3->beat_adj = (next_beat - phase4->beat)/ phase3->tot_frames;
                phase3->amp_adj = (next_amp - phase4->amp)/ phase3->tot_frames;
                phase3->phase_adj = (next_phase - phase4->phase)/ phase3->tot_frames;
                /* Amplitude beats are optional.  If there isn't a match, treat as zero instead */
                if (next_amp_beat1 > 0.0)
                  phase3->amp_beat1_adj = (next_amp_beat1 - phase4->amp_beat1)/ phase3->tot_frames;
                else  // zero amp_beat1 in next phase
                  phase3->amp_beat1_adj = - phase4->amp_beat1 / phase3->tot_frames;
                if (next_amp_beat2 > 0.0)
                  phase3->amp_beat2_adj = (next_amp_beat2 - phase4->amp_beat2)/ phase3->tot_frames;
                else  // zero amp_beat2 in next phase
                  phase3->amp_beat2_adj = - phase4->amp_beat2 / phase3->tot_frames;
                /* Amplitude percents are optional.  If there isn't a match, treat as zero instead */
                if (next_amp_pct1 > 0.0)
                  phase3->amp_pct1_adj = (next_amp_pct1 - phase4->amp_pct1)/ phase3->tot_frames;
                else  // zero amp_pct1 in next phase
                  phase3->amp_pct1_adj = - phase4->amp_pct1 / phase3->tot_frames;
                if (next_amp_pct2 > 0.0)
                  phase3->amp_pct2_adj = (next_amp_pct2 - phase4->amp_pct2)/ phase3->tot_frames;
                else  // zero amp_pct2 in next phase
                  phase3->amp_pct2_adj = - phase4->amp_pct2 / phase3->tot_frames;
              } 
              else  // a step
              {
                memcpy ((void *) phase3, (void *) phase1, sizeof (phase)); // copy first in list to it
                /* Set values used for calculation in last slide */
                phase3->carrier = next_carrier;
                phase3->beat = next_beat;
                phase3->amp = next_amp;
                phase3->phase = next_phase;
                phase3->amp_beat1 = next_amp_beat1;
                phase3->amp_beat2 = next_amp_beat2;
                phase3->amp_pct1 = next_amp_pct1;
                phase3->amp_pct2 = next_amp_pct2;
              }
              phase4->step_next = phase3;  // set list pointer for previous node
              phase3->last_off1 = &(phase4->off1);  // each node starts where last left off as offset
              phase3->last_amp_off1 = &(phase4->amp_off1);  // each node starts where last left off as amp_offset
              phase3->last_amp_off2 = &(phase4->amp_off2);
              phase3->last_shift = &(phase4->shift);  // each node starts where last left off for phase and direction
              phase3->last_direction = &(phase4->direction);
              phase4 = phase3;  // make current node previous node
            }
            break;
          }
        case 19:  // fm
          { 
            fm *fm1 = NULL, *fm2 = NULL;

            fm1 = (fm *) work1;
            fm1->off1 = fm1->inc1 = 0;
            fm1->amp_off1 = fm1->amp_inc1 = fm1->amp_off2 = fm1->amp_inc2 = 0;
            if (work2 != NULL)
            { 
              stub2 = (stub *) work2;
              if (stub2->type == 19 || stub2->type == 20 || stub2->type == 21)  // also fm
              { 
                fm2 = (fm *) work2;
                /* Set the pointers to the previous voice's offsets here so it can be used while running.
                   Need to do this even when there is no slide.  Some duplication with below. */
                fm2->last_off1 = &(fm1->off1);
                fm2->last_amp_off1 = &(fm1->amp_off1);
                fm2->last_amp_off2 = &(fm1->amp_off2);
                fm2->last_shift = &(fm1->shift);
                fm2->last_direction = &(fm1->direction);
              } 
            } 
            if (fm1->slide == 0)
            { 
              fm1->carr_adj = fm1->beat_adj = fm1->amp_adj = fm1->phase_adj = 0.0;
              fm1->band_adj = 0.0;
              fm1->amp_beat1_adj = fm1->amp_beat2_adj = 0.0;
              fm1->amp_pct1_adj = fm1->amp_pct2_adj = 0.0;
            } 
            else  // slide to next fm in stream
            { 
              if (work2 != NULL)
              { 
                if (fm2 != NULL)  // set above if fm, NULL means next voice not fm
                {
                  fm1->carr_adj = (fm2->carrier - fm1->carrier)/ (double) snd1->tot_frames;
                  fm1->beat_adj = (fm2->beat - fm1->beat)/ (double) snd1->tot_frames;
                  fm1->amp_adj = (fm2->amp - fm1->amp)/ (double) snd1->tot_frames;
                  fm1->phase_adj = (fm2->phase - fm1->phase)/ (double) snd1->tot_frames;
                  fm1->band_adj = (fm2->band - fm1->band)/ (double) snd1->tot_frames;
                  /* Amplitude beats are optional.  If there isn't a match, treat as zero instead */
                  if (fm2->amp_beat1 > 0.0)
                    fm1->amp_beat1_adj = (fm2->amp_beat1 - fm1->amp_beat1)/ (double) snd1->tot_frames;
                  else  // zero amp_beat1 in next fm
                    fm1->amp_beat1_adj = - fm1->amp_beat1 / (double) snd1->tot_frames;
                  if (fm2->amp_beat2 > 0.0)
                    fm1->amp_beat2_adj = (fm2->amp_beat2 - fm1->amp_beat2)/ (double) snd1->tot_frames;
                  else  // zero amp_beat2 in next fm
                    fm1->amp_beat2_adj = - fm1->amp_beat2 / (double) snd1->tot_frames;
                  /* Amplitude percents are optional.  If there isn't a match, treat as zero instead */
                  if (fm2->amp_pct1 > 0.0)
                    fm1->amp_pct1_adj = (fm2->amp_pct1 - fm1->amp_pct1)/ (double) snd1->tot_frames;
                  else  // zero amp_pct1 in next fm
                    fm1->amp_pct1_adj = - fm1->amp_pct1 / (double) snd1->tot_frames;
                  if (fm2->amp_pct2 > 0.0)
                    fm1->amp_pct2_adj = (fm2->amp_pct2 - fm1->amp_pct2)/ (double) snd1->tot_frames;
                  else  // zero amp_pct2 in next fm
                    fm1->amp_pct2_adj = - fm1->amp_pct2 / (double) snd1->tot_frames;
                } 
                else
                  error ("Slide called for, voice to slide to is not fm.  Position matters!\n");
              } 
              else
                error ("Slide called for, no next fm in time sequence!\n");
            }
            break;
          }
        case 20:  // fm step slide, have to create list of steps and slides
          { 
            fm *fm1 = NULL, *fm2 = NULL, *fm3 = NULL, *fm4 = NULL;

            fm1 = (fm *) work1;
            fm1->off1 = fm1->inc1 = 0;
            fm1->amp_off1 = fm1->amp_inc1 = fm1->amp_off2 = fm1->amp_inc2 = 0;
             /* First step is always the input frequency, so no adjust. */
            fm1->carr_adj = fm1->beat_adj = fm1->amp_adj = fm1->phase_adj = 0.0;
            fm1->band_adj = 0.0;
            fm1->amp_beat1_adj = fm1->amp_beat2_adj = 0.0;
            fm1->amp_pct1_adj = fm1->amp_pct2_adj = 0.0;
            /* Determine the step and slide frame sizes.  */
            int_64 slide_frames = (int_64) (out_rate * fm1->slide_time);  // frames in each slide
            int_64 total_slide = (int_64) (slide_frames * fm1->steps);  //  total slide time
            int_64 step_frames = (snd1->tot_frames - total_slide) / fm1->steps;  // frames in each step
            /*  Leftover frames after all step slides determined.  Add to last step. The total number
             *  of frames in the list has to be exactly the number of frames in the current time sequence. */
            int_64 frame_residue = (snd1->tot_frames - total_slide - (step_frames * fm1->steps));
            fm1->tot_frames = step_frames;
            fm1->cur_frames = 0;  // fm1 complete except for step list pointer set below.
            if (work2 != NULL)  // determine fm we are step sliding to so steps and slides can be set up
            { 
              stub2 = (stub *) work2;
              if (stub2->type == 19 || stub2->type == 20 || stub2->type == 21)  // also fm
                fm2 = (fm *) work2;
              else
                error ("Step slide called for, voice to slide to is not fm.  Position matters!\n");
            } 
            else
              error ("Step slide called for, no next fm in time sequence!\n");
            double carr_diff = (fm2->carrier - fm1->carrier);
            double beat_diff = (fm2->beat - fm1->beat);
            double amp_diff = (fm2->amp - fm1->amp);
            double phase_diff = (fm2->phase - fm1->phase);
            double band_diff = (fm2->band - fm1->band);
            double amp_beat1_diff = (fm2->amp_beat1 - fm1->amp_beat1);
            double amp_beat2_diff = (fm2->amp_beat2 - fm1->amp_beat2);
            double amp_pct1_diff = (fm2->amp_pct1 - fm1->amp_pct1);
            double amp_pct2_diff = (fm2->amp_pct2 - fm1->amp_pct2);
            double next_carrier = 0.0;
            double next_beat = 0.0;
            double next_amp = 0.0;
            double next_phase = 0.0;
            double next_band = 0.0;
            double next_amp_beat1 = 0.0;
            double next_amp_beat2 = 0.0;
            double next_amp_pct1 = 0.0;
            double next_amp_pct2 = 0.0;
            fm4 = fm1;  // set last node processed
            int total_nodes = (2 * fm1->steps);
            int ii;
            for (ii = 1; ii < total_nodes; ii++)  // create rest of step list nodes
            {
              fm3 = (fm *) Alloc ((sizeof (fm)) * 1);  // create next node of step list
              if (ii % 2 == 1)  // a slide
              {
                memcpy ((void *) fm3, (void *) fm4, sizeof (fm)); // copy last step
                fm3->tot_frames = slide_frames;
                if (ii == total_nodes - 1)  // last slide, to next time sequence voice fm2
                {
                  fm2->last_off1 = &(fm3->off1);
                  fm2->last_amp_off1 = &(fm3->amp_off1);
                  fm2->last_amp_off2 = &(fm3->amp_off2);
                  fm2->last_shift = &(fm3->shift);
                  fm2->last_direction = &(fm3->direction);
                  next_carrier = fm2->carrier;
                  next_beat = fm2->beat;
                  next_amp = fm2->amp;
                  next_phase = fm2->phase;
                  next_band = fm2->band;
                  next_amp_beat1 = fm2->amp_beat1;
                  next_amp_beat2 = fm2->amp_beat2;
                  next_amp_pct1 = fm2->amp_pct1;
                  next_amp_pct2 = fm2->amp_pct2;
                  fm3->step_next = NULL;  // last node, no next node
                }
                else  // internal slide
                {
                  double fraction = ((double) (ii+1)/(double) total_nodes);  // fraction of interval
                  next_carrier = fm1->carrier + (carr_diff * fraction);
                  next_beat = fm1->beat + (beat_diff * fraction);
                  next_amp = fm1->amp + (amp_diff * fraction);
                  next_phase = fm1->phase + (phase_diff * fraction);
                  next_band = fm1->band + (band_diff * fraction);
                  next_amp_beat1 = fm1->amp_beat1 + (amp_beat1_diff * fraction);
                  next_amp_beat2 = fm1->amp_beat2 + (amp_beat2_diff * fraction);
                  next_amp_pct1 = fm1->amp_pct1 + (amp_pct1_diff * fraction);
                  next_amp_pct2 = fm1->amp_pct2 + (amp_pct2_diff * fraction);
                  if (fm1->fuzz > 0.0)  // fuzz the interval
                  {
                    double adjust = drand48() - 0.5;  // fuzz adjustment between -.5 and +.5 of fuzz
                    next_carrier += ((carr_diff/fm1->steps) * fm1->fuzz * adjust);
                    next_beat += ((beat_diff/fm1->steps) * fm1->fuzz * adjust);
                    next_amp += ((amp_diff/fm1->steps) * fm1->fuzz * adjust);
                    next_phase += ((phase_diff/fm1->steps) * fm1->fuzz * adjust);
                    next_band += ((band_diff/fm1->steps) * fm1->fuzz * adjust);
                    next_amp_beat1 += ((amp_beat1_diff/fm1->steps) * fm1->fuzz * adjust);
                    next_amp_beat2 += ((amp_beat2_diff/fm1->steps) * fm1->fuzz * adjust);
                    next_amp_pct1 += ((amp_pct1_diff/fm1->steps) * fm1->fuzz * adjust);
                    next_amp_pct2 += ((amp_pct2_diff/fm1->steps) * fm1->fuzz * adjust);
                  }
                }
                fm3->carr_adj = (next_carrier - fm4->carrier)/ fm3->tot_frames;
                fm3->beat_adj = (next_beat - fm4->beat)/ fm3->tot_frames;
                fm3->amp_adj = (next_amp - fm4->amp)/ fm3->tot_frames;
                fm3->phase_adj = (next_phase - fm4->phase)/ fm3->tot_frames;
                fm3->band_adj = (next_band - fm4->band)/ fm3->tot_frames;
                /* Amplitude beats are optional.  If there isn't a match, treat as zero instead */
                if (next_amp_beat1 > 0.0)
                  fm3->amp_beat1_adj = (next_amp_beat1 - fm4->amp_beat1)/ fm3->tot_frames;
                else  // zero amp_beat1 in next fm
                  fm3->amp_beat1_adj = - fm4->amp_beat1 / fm3->tot_frames;
                if (next_amp_beat2 > 0.0)
                  fm3->amp_beat2_adj = (next_amp_beat2 - fm4->amp_beat2)/ fm3->tot_frames;
                else  // zero amp_beat2 in next fm
                  fm3->amp_beat2_adj = - fm4->amp_beat2 / fm3->tot_frames;
                /* Amplitude percents are optional.  If there isn't a match, treat as zero instead */
                if (next_amp_pct1 > 0.0)
                  fm3->amp_pct1_adj = (next_amp_pct1 - fm4->amp_pct1)/ fm3->tot_frames;
                else  // zero amp_pct1 in next fm
                  fm3->amp_pct1_adj = - fm4->amp_pct1 / fm3->tot_frames;
                if (next_amp_pct2 > 0.0)
                  fm3->amp_pct2_adj = (next_amp_pct2 - fm4->amp_pct2)/ fm3->tot_frames;
                else  // zero amp_pct2 in next fm
                  fm3->amp_pct2_adj = - fm4->amp_pct2 / fm3->tot_frames;
              } 
              else  // a step
              {
                memcpy ((void *) fm3, (void *) fm1, sizeof (fm)); // copy first in list to it
                if (ii == (total_nodes - 2))
                  fm3->tot_frames += frame_residue;  // use up leftover frames in last step
                /* Set values used for calculation in last slide */
                fm3->carrier = next_carrier;
                fm3->beat = next_beat;
                fm3->amp = next_amp;
                fm3->phase = next_phase;
                fm3->band = next_band;
                fm3->amp_beat1 = next_amp_beat1;
                fm3->amp_beat2 = next_amp_beat2;
                fm3->amp_pct1 = next_amp_pct1;
                fm3->amp_pct2 = next_amp_pct2;
              }
              fm4->step_next = fm3;  // set list pointer for previous node
              fm3->last_off1 = &(fm4->off1);  // each node starts where last left off as offset
              fm3->last_amp_off1 = &(fm4->amp_off1);  // each node starts where last left off as amp_offset
              fm3->last_amp_off2 = &(fm4->amp_off2);
              fm3->last_shift = &(fm4->shift);  // each node starts where last left off for phase and direction
              fm3->last_direction = &(fm4->direction);
              fm4 = fm3;  // make current node previous node
            }
            break;
          }
        case 21:  // fm vary slide, have to create list of steps and slides
          { 
            fm *fm1 = NULL, *fm2 = NULL, *fm3 = NULL, *fm4 = NULL;

            fm1 = (fm *) work1;
            fm1->off1 = fm1->inc1 = 0;
            fm1->amp_off1 = fm1->amp_inc1 = fm1->amp_off2 = fm1->amp_inc2 = 0;
             /* First step is always the input frequency, so no adjust. */
            fm1->carr_adj = fm1->beat_adj = fm1->amp_adj = fm1->phase_adj = 0.0;
            fm1->band_adj = 0.0;
            fm1->amp_beat1_adj = fm1->amp_beat2_adj = 0.0;
            fm1->amp_pct1_adj = fm1->amp_pct2_adj = 0.0;
            /* Determine the step and slide frame sizes.  */
            int_64 slide_frames = (int_64) (out_rate * fm1->slide_time);  // frames in each slide
            int_64 total_slide = (int_64) (slide_frames * fm1->steps);  //  total slide time
            int_64 step_frames = (snd1->tot_frames - total_slide) / fm1->steps;  // frames in each step
            /*  Leftover frames after all step slides determined.  Add to last slide. The total number
             *  of frames in the list has to be exactly the number of frames in the current time sequence. */
            int_64 frame_residue = (snd1->tot_frames - total_slide - (step_frames * fm1->steps));
            fm1->tot_frames = step_frames;
            fm1->cur_frames = 0;  // fm1 complete except for step list pointer set below.
            if (work2 != NULL)  // determine fm we are step sliding to so steps and slides can be set up
            { 
              stub2 = (stub *) work2;
              if (stub2->type == 19 || stub2->type == 20 || stub2->type == 21)  // also fm
                fm2 = (fm *) work2;
              else
                error ("Vary slide called for, voice to slide to is not fm.  Position matters!\n");
            } 
            else
              error ("Vary slide called for, no next fm in time sequence!\n");
            double carr_diff = (fm2->carrier - fm1->carrier);
            double beat_diff = (fm2->beat - fm1->beat);
            double amp_diff = (fm2->amp - fm1->amp);
            double phase_diff = (fm2->phase - fm1->phase);
            double band_diff = (fm2->band - fm1->band);
            double amp_beat1_diff = (fm2->amp_beat1 - fm1->amp_beat1);
            double amp_beat2_diff = (fm2->amp_beat2 - fm1->amp_beat2);
            double amp_pct1_diff = (fm2->amp_pct1 - fm1->amp_pct1);
            double amp_pct2_diff = (fm2->amp_pct2 - fm1->amp_pct2);
            double next_carrier = 0.0;
            double next_beat = 0.0;
            double next_amp = 0.0;
            double next_phase = 0.0;
            double next_band = 0.0;
            double next_amp_beat1 = 0.0;
            double next_amp_beat2 = 0.0;
            double next_amp_pct1 = 0.0;
            double next_amp_pct2 = 0.0;
            fm4 = fm1;  // set last node processed
            int total_nodes = (2 * fm1->steps);
            int ii;
            for (ii = 1; ii < total_nodes; ii++)  // create rest of vary list nodes
            {
              fm3 = (fm *) Alloc ((sizeof (fm)) * 1);  // create next node of vary list
              if (ii % 2 == 1)  // a slide
              {
                memcpy ((void *) fm3, (void *) fm4, sizeof (fm)); // copy last step
                fm3->tot_frames = slide_frames;
                if (ii == total_nodes - 1)  // last slide, to next time sequence voice fm2
                {
                  fm2->last_off1 = &(fm3->off1);  // fm2 will start from these offsets
                  fm2->last_amp_off1 = &(fm3->amp_off1);  // fm2 will start from these amp_offsets
                  fm2->last_amp_off2 = &(fm3->amp_off2);
                  fm2->last_shift = &(fm3->shift);
                  fm2->last_direction = &(fm3->direction);
                  next_carrier = fm2->carrier;
                  next_beat = fm2->beat;
                  next_amp = fm2->amp;
                  next_phase = fm2->phase;
                  next_band = fm2->band;
                  next_amp_beat1 = fm2->amp_beat1;
                  next_amp_beat2 = fm2->amp_beat2;
                  next_amp_pct1 = fm2->amp_pct1;
                  next_amp_pct2 = fm2->amp_pct2;
                  fm3->step_next = NULL;  // last node, no next node
                  fm3->tot_frames += frame_residue;  // use up leftover frames in last slide
                }
                else  // internal slide
                {
                  double fraction = drand48 ();  // random fraction of interval
                  next_carrier = fm1->carrier + (carr_diff * fraction);
                  next_beat = fm1->beat + (beat_diff * fraction);
                  next_amp = fm1->amp + (amp_diff * fraction);
                  next_phase = fm1->phase + (phase_diff * fraction);
                  next_band = fm1->band + (band_diff * fraction);
                  next_amp_beat1 = fm1->amp_beat1 + (amp_beat1_diff * fraction);
                  next_amp_beat2 = fm1->amp_beat2 + (amp_beat2_diff * fraction);
                  next_amp_pct1 = fm1->amp_pct1 + (amp_pct1_diff * fraction);
                  next_amp_pct2 = fm1->amp_pct2 + (amp_pct2_diff * fraction);
                }
                fm3->carr_adj = (next_carrier - fm4->carrier)/ fm3->tot_frames;
                fm3->beat_adj = (next_beat - fm4->beat)/ fm3->tot_frames;
                fm3->amp_adj = (next_amp - fm4->amp)/ fm3->tot_frames;
                fm3->phase_adj = (next_phase - fm4->phase)/ fm3->tot_frames;
                fm3->band_adj = (next_band - fm4->band)/ fm3->tot_frames;
                /* Amplitude beats are optional.  If there isn't a match, treat as zero instead */
                if (next_amp_beat1 > 0.0)
                  fm3->amp_beat1_adj = (next_amp_beat1 - fm4->amp_beat1)/ fm3->tot_frames;
                else  // zero amp_beat1 in next fm
                  fm3->amp_beat1_adj = - fm4->amp_beat1 / fm3->tot_frames;
                if (next_amp_beat2 > 0.0)
                  fm3->amp_beat2_adj = (next_amp_beat2 - fm4->amp_beat2)/ fm3->tot_frames;
                else  // zero amp_beat2 in next fm
                  fm3->amp_beat2_adj = - fm4->amp_beat2 / fm3->tot_frames;
                /* Amplitude percents are optional.  If there isn't a match, treat as zero instead */
                if (next_amp_pct1 > 0.0)
                  fm3->amp_pct1_adj = (next_amp_pct1 - fm4->amp_pct1)/ fm3->tot_frames;
                else  // zero amp_pct1 in next fm
                  fm3->amp_pct1_adj = - fm4->amp_pct1 / fm3->tot_frames;
                if (next_amp_pct2 > 0.0)
                  fm3->amp_pct2_adj = (next_amp_pct2 - fm4->amp_pct2)/ fm3->tot_frames;
                else  // zero amp_pct2 in next fm
                  fm3->amp_pct2_adj = - fm4->amp_pct2 / fm3->tot_frames;
              } 
              else  // a step
              {
                memcpy ((void *) fm3, (void *) fm1, sizeof (fm)); // copy first in list to it
                /* Set values used for calculation in last slide */
                fm3->carrier = next_carrier;
                fm3->beat = next_beat;
                fm3->amp = next_amp;
                fm3->phase = next_phase;
                fm3->band = next_band;
                fm3->amp_beat1 = next_amp_beat1;
                fm3->amp_beat2 = next_amp_beat2;
                fm3->amp_pct1 = next_amp_pct1;
                fm3->amp_pct2 = next_amp_pct2;
              }
              fm4->step_next = fm3;  // set list pointer for previous node
              fm3->last_off1 = &(fm4->off1);  // each node starts where last left off as offset
              fm3->last_amp_off1 = &(fm4->amp_off1);  // each node starts where last left off as amp_offset
              fm3->last_amp_off2 = &(fm4->amp_off2);
              fm3->last_shift = &(fm4->shift);  // each node starts where last left off for phase and direction
              fm3->last_direction = &(fm4->direction);
              fm4 = fm3;  // make current node previous node
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

/* Take care of importing a sound file.  Check if it is already imported.
 * If it is return a pointer to the sound buffer.  If it isn't, check if
 * it needs to be resampled and then create a snd_buffer node for it
 * in the Sound_Files list.  Return a pointer to that node.
 */
snd_buffer * 
process_sound_file (char *filename)
{
  snd_buffer *sb1 = NULL;
  SNDFILE *sndfile;
  SF_INFO sfinfo;
  sf_count_t num_frames;
  int subformat ;
  short holder, peak=0;
  int k;

  if (Sound_Files != NULL)
  {
    sb1 = Sound_Files;
    do
    {
      if (strcmp (sb1->filename, filename) == 0)
        return sb1;  // file already processed
      else
        sb1 = sb1->next;
    }while (sb1 != NULL);
  }
  /* file not already processed, create a new node for it */
  sb1 = (snd_buffer *) Alloc (sizeof (snd_buffer) * 1);
  if (Sound_Files == NULL)       // no buffer files yet, make root node
  {
    sb1->next = NULL;
    sb1->prev = NULL;
  }
  else  // insert at front of list
  {
    sb1->next = Sound_Files;
    sb1->prev = NULL;
    Sound_Files->prev = sb1;
  }
  Sound_Files = sb1;
  sb1->filename = StrDup (filename); // save name before possible modification below
  /* if filename is not same rate as out_rate, resample to new file.
   * Modifies filename by addition of samplerate.
   */
  long flag = check_samplerate (filename);  
  if (! (sndfile = sf_open (filename, SFM_READ, &sfinfo)))
    error ("Couldn't open input sound file %s\n", filename);
  if (sfinfo.channels == 1)
  {
    sb1->channels = sfinfo.channels;  // mono
    sb1->mono = 1;  // mono
  }
  else if (sfinfo.channels == 2)  // check if mono in stereo format
  {
    sb1->channels = 2;  // stereo channels
    double peaks[2];
    int retval = sf_command (sndfile, SFC_CALC_MAX_ALL_CHANNELS, peaks, sizeof (peaks));
    if (retval == 0)
      if (peaks [0] < 1e-10)  // a mute channel
        sb1->mono = 2;  // right channel has sound
      else if (peaks [1] < 1e-10)  // a mute channel
        sb1->mono = 1;  // left channel has sound
      else if (peaks[0] / peaks [1] > 100)  // large imbalance
        sb1->mono = 1;  // left channel has sound
      else if (peaks[1] / peaks [0] > 100)  // large imbalance
        sb1->mono = 2;  // right channel has sound
      else
        sb1->mono = 0;
    else
      sb1->mono = 0;
  }
  else
    error ("Import sound file %s has incorrect number of channels %d\n", 
            filename, sfinfo.channels);
  num_frames = sfinfo.frames;
  sb1->frames = num_frames;
  sb1->sound = (short *) Alloc ((sizeof (short)) * num_frames * sfinfo.channels);
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
    num_frames = sf_readf_short (sndfile, sb1->sound, sb1->frames);
  }
  else // reading into short
    num_frames = sf_readf_short (sndfile, sb1->sound, sb1->frames);
  if (num_frames != sb1->frames)
    error ("Read incorrect number of frames for sound file %s, %ld instead of %ld\n", 
            filename, num_frames, sb1->frames);
  sf_close (sndfile);
  if (flag != 0 && opt_k == 0)
  {  // if resampled and not keep option remove resampled file
    char command [4096];
    strcpy (command, "rm ");
    strcat (command, filename);
    system (command);
  }
  /* find the maximum amplitude in the sound file, always short int once read */
  for (k = 0 ; k < sb1->frames ; k += sb1->channels)
  { 
    holder = abs (sb1->sound [k]) ;
    peak  = holder > peak ? holder : peak ;
    if (sb1->channels == 2)
    {
      holder = abs (sb1->sound [k+1]) ;
      peak  = holder > peak ? holder : peak ;
    }
  } 
  // scale factor is 1 divided by maximum amplitude in file
  sb1->scale = 1.0 / ((double) peak + 10.0); // 10 ensures no clipping
  return sb1;
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
  if (alsa_dev == NULL)
    error("Could not open the sound device\n");
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
  if (!opt_q && snd1 != NULL)  // not quiet, sound to display
  {
      /* block until previous status operation complete, unlocked in status_t */
    pthread_mutex_lock (&mtx_status);
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
      snd1->cur_frames += (fade_length * fast_mult);  // adjust frames so far in this sound stream
      if (!opt_d)
      {
        if (opt_t)  // use thread to play
        {
          sound_slice->frames = offset; // number of frames in buffer
            /* block until previous play operation complete, unlocked in alsa_write */
          pthread_mutex_lock (&mtx_play);  
          memcpy (play_buffer, buffer, sizeof(buffer));  // copy frames to play
              /* this create is non blocking, continue creating frames to play */
          pthread_create (&pth_play, &attr_play, (void *) &alsa_write, (void *) sound_slice);
        }
        else  // blocking function call
            /* send doubles to alsa-lib to translate to sound card format and play */
          alsa_write_retval = alsa_write_double (alsa_dev, buffer, offset, channels) ;
      }
      display_frames += (fade_length * fast_mult);  // adjust display frames
      if (!opt_q && display_frames >= display_count)   // not quiet,  time to display
      {
          /* block until previous status operation complete, unlocked in status_t */
        pthread_mutex_lock (&mtx_status);
          /* this create is non blocking, continue creating frames to play */
        pthread_create (&pth_status, &attr_status, (void *) &status_t, (void *) snd_point);
        display_frames = 0L;
      }
      offset = 0;
    }
    snd2 = snd1->next;  // move to next time period
    snd1 = snd2;
    if (snd1 == NULL)
      break;  // finished all time periods, out of the loop
  }
  sleep (1);  // allows playing thread to finish before shutdown
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
  if (checkval != SF_TRUE)
    error ("Format and bit rate not supported by libsndfile");
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
  if (!opt_q && snd1 != NULL)  // not quiet, sound to display
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
      snd1->cur_frames += (fade_length * fast_mult);  // adjust frames so far in this sound stream
      if (!opt_d)
      {
        sound_slice->frames = offset; // number of frames in buffer
          /* block until previous write operation complete, released by file_write */
        pthread_mutex_lock (&mtx_write);
        memcpy (write_buffer, buffer, sizeof(buffer));  // copy frames to write
            /* this create is non blocking, continue creating frames to write */
        pthread_create (&pth_write, &attr_write, (void *) &file_write, (void *) sound_slice);
      }
      display_frames += (fade_length * fast_mult);  // adjust display frames
      if (!opt_q && display_frames >= display_count)  // not quiet and time to display
      {
          /* block until previous status operation complete, released by status_t */
        pthread_mutex_lock (&mtx_status);
          /* this create is non blocking, continue creating frames to write */
        pthread_create (&pth_status, &attr_status, (void *) &status_t, (void *) snd_point);
        display_frames = 0L;
      }
      offset = 0;
    }
    snd2 = snd1->next;  // move to next time period
    snd1 = snd2;
    if (snd1 == NULL)
      break;  // finished all time periods, out of the loop
  }
  sleep (1);  // allows writing thread to finish before shutdown
  sf_close (sndfile);
}

/* Generate the number of frames of data requested,
   combining each voice in current period */
int
generate_frames (struct sndstream *snd1, double *out_buffer, int offset, int frame_count)
{
  int ii;
  int sin_siz = 2 * out_rate;
  int channels = 2;  // always output stereo
  stub *stub1;
  void *this, *next;
  int_64 remaining_frames = snd1->tot_frames - snd1->cur_frames;

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
            if (binaural1->last_amp_off1 != NULL)  // there *is* a previous amp_offset to use
              binaural1->amp_off1 = *binaural1->last_amp_off1;  // to eliminate crackle from discontinuity in wave
            if (binaural1->last_amp_off2 != NULL)  // there *is* a previous amp_offset to use
              binaural1->amp_off2 = *binaural1->last_amp_off2;
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
              binaural1->beat += (binaural1->beat_adj * fast_mult);
              binaural1->amp += (binaural1->amp_adj * fast_mult);
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
              bell1->off1 = 0;
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
              if ((remaining_frames - bell1->next_play) < bell1->length_min )  // never run past end of voice
              {
                bell1->next_play = remaining_frames + 1;
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
              if (bell1->ring > remaining_frames)  // never run past end of voice
              {
                if (bell1->ring > bell1->length_min)
                  bell1->ring = remaining_frames;
                else
                  bell1->ring = 0LL;
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
                bell1->amp *= amp_comp (bell1->carrier) * 2.;  // like binaural, double so each channel at amp
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
            if (bell1->ring > 0LL)
            {
              out_buffer[ii] += bell1->split_now * bell1->amp * sin_table[bell1->off1];
              out_buffer[ii+1] += (1.0 - bell1->split_now) * bell1->amp * sin_table[bell1->off1];
              //bell1->inc1 = (( (bell1->carrier * (out_rate * 2)) / out_rate));  // what below actually is
              bell1->inc1 = (int) round( bell1->carrier * 2.);
              bell1->off1 += bell1->inc1;
              bell1->off1 = bell1->off1 % (out_rate * 2);
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
      case 3:                // noise
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
              noise1->off1 = 0;  // always start at 0 so sin value == 0.0, thus no fade in
              noise1->fade_factor = 1.0;  // play at full volume until ending fade out
              /* first determine the play length for this tone.
                 has to be first as the next play depends on it. */
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
                noise1->amp *= amp_comp (noise1->carrier) * 2.;  // like binaural, double so each channel at amp with split
              if (noise1->behave_low == noise1->behave_high)
              {                   // fixed decay behavior
                noise1->behave = noise1->behave_low;
              }
              else // choose decay style for noise1 tone
              {
                int diff = (noise1->behave_high - noise1->behave_low) + 1;
                noise1->behave = noise1->behave_low + (int) (rand () % diff);
              }
              /* how the tone behaves while it is playing has become complex.
               * Both carrier and amplitude can change.
               */
              switch (noise1->behave)  // adjust the carrier frequency portion of behave
              {
                case 8:   // 10% carrier drop
                case 9:
                case 10:
                case 11:
                case 12:
                case 13:
                case 14:
                  noise1->carrier_adj = -(noise1->carrier * .10) / ((double) noise1->play);
                  break;
                case 15:   // 10% carrier rise
                case 16:
                case 17:
                case 18:
                case 19:
                case 20:
                case 21:
                  noise1->carrier_adj = (noise1->carrier * .10) / ((double) noise1->play);
                  break;
                default:
                  noise1->carrier_adj = 0.0;
              }
              switch (noise1->behave)  // adjust amplitude portion of behave
              {
                case 1:   // linear reduce to .50
                case 8: 
                case 15:
                  noise1->amp_adj = - (noise1->amp * .50) / ((double) noise1->play);
                  break;
                case 2:      // linear reduce to .90
                case 9:
                case 16:
                  noise1->amp_adj = - (noise1->amp * .10) / ((double) noise1->play);
                  break;
                case 3:     // no change
                case 10:
                case 17:
                  noise1->amp_adj = 0.0;
                  break;
                case 4:      // linear enhance to 1.10
                case 11:
                case 18:
                  noise1->amp_adj = (noise1->amp * .10) / ((double) noise1->play);
                  break;
                case 5:      // linear enhance to 1.50
                case 12:
                case 19:
                  noise1->amp_adj = (noise1->amp * .50) / ((double) noise1->play);
                  break;
                case 6:      // follow first half of sine wave, +ve
                case 13:
                case 20:
                  {
                    noise1->behave_off1 = 0.0;
                    /* Sin table twice sample rate in size, half is sample_rate in size.
                     * Want to traverse first pi of it over the course of the noise play */
                    noise1->behave_inc1 = ((double) out_rate) / ((double) noise1->play);
                  }
                  break;
                case 7:      // follow second half of sine wave, -ve
                case 14:
                case 21:
                  {
                    noise1->behave_off1 = (double) out_rate;
                    /* Sin table twice sample rate in size, half is sample_rate in size.
                     * Want to traverse last pi of it over the course of the noise play */
                    noise1->behave_inc1 = ((double) out_rate) / ((double) noise1->play);
                  }
                  break;
                default:
                  noise1->amp_adj = 0.0;
              }
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
              /* adjust carrier if behave requires it before setting new sin table offset value */
              if (noise1->behave >= 8 && noise1->behave <= 21)
                noise1->carrier += noise1->carrier_adj;
              double sin_factor;  // used for sinusoidal adjustment to amplitude
              /* check for sinusoidal behavior */
              if (noise1->behave == 6 || noise1->behave == 13 || noise1->behave == 20)
                sin_factor = 0.25 + sin_table [(int) noise1->behave_off1];  // increase to 1.25 of start as hump
              else if (noise1->behave == 7 || noise1->behave == 14 || noise1->behave == 21)
                sin_factor = 1.0 + (0.5 * sin_table [(int) noise1->behave_off1]);  // drop only to half amplitude as bowl
              else
                sin_factor = 1.0;  // default to standard behavior
              if (noise1->play  > msec_fade_count)  // in play range before fade out
              {
                out_buffer[ii] += noise1->split_now * noise1->amp * sin_factor * sin_table[noise1->off1];
                out_buffer[ii+1] += (1.0 - noise1->split_now) * noise1->amp * sin_factor * sin_table[noise1->off1];
              }
              else  // 1 millisec fade out to reduce crackle at end, no fade in because start at zero
              {
                noise1->fade_factor -= msec_fade_adjust;  // ramp down from 1.0 to 0.0
                out_buffer[ii] += (noise1->split_now * noise1->amp * sin_factor * sin_table[noise1->off1]
                                   * noise1->fade_factor);
                out_buffer[ii+1] += ((1.0 - noise1->split_now) * noise1->amp * sin_factor * sin_table[noise1->off1]
                                   * noise1->fade_factor);
              }
              /* Move offset adjustment to end so always start at offset where sin == 0.0, thus no fade in */
              //noise1->inc1 = (( (noise1->carrier * (out_rate * 2)) / out_rate));  // what below actually is
              noise1->inc1 = (int) round( noise1->carrier * 2.);
              noise1->off1 += noise1->inc1;
              noise1->off1 = noise1->off1 % (out_rate * 2);
              if (noise1->behave >= 1 && noise1->behave <= 5)
                noise1->amp += (noise1->amp_adj * fast_mult);
              else  // sinusoidal behavior, digital approximation
                noise1->behave_off1 += (noise1->behave_inc1 * fast_mult);
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
                int_64 delta = (int_64) ( (drand48 ()) * (stoch1->repeat_max - stoch1->repeat_min));
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
              /* adjust per frame */
              stoch1->split_adj = (split_end - stoch1->split_now) / (double) stoch1->play;
            }
            if (stoch1->play > 0L)  // stoch is active
            {
              double amp = stoch1->amp * 2.;  // like binaural, double so each channel at amp with split
              if (stoch1->channels == 2)  // stereo
              {
                if (stoch1->mono == 0)  // stereo
                {
                  out_buffer[ii] += (stoch1->split_now * amp
                          * (((double) *(stoch1->sound + stoch1->off1)) * stoch1->scale));
                  out_buffer[ii+1] += ((1.0 - stoch1->split_now) * amp
                          * (((double) *(stoch1->sound + stoch1->off1 + 1)) * stoch1->scale));
                }
                else if (stoch1->mono == 1)  // mono in stereo form, left has sound, stoch left as right channel
                {
                  out_buffer[ii] += (stoch1->split_now * amp
                          * (((double) *(stoch1->sound + stoch1->off1)) * stoch1->scale));
                  out_buffer[ii+1] += ((1.0 - stoch1->split_now) * amp
                          * (((double) *(stoch1->sound + stoch1->off1)) * stoch1->scale));
                }
                else if (stoch1->mono == 2)  // mono in stereo form, right has sound, stoch right as left channel
                {
                  out_buffer[ii] += (stoch1->split_now * amp
                          * (((double) *(stoch1->sound + stoch1->off1 + 1)) * stoch1->scale));
                  out_buffer[ii+1] += ((1.0 - stoch1->split_now) * amp
                          * (((double) *(stoch1->sound + stoch1->off1 + 1)) * stoch1->scale));
                }
              }
              else if (stoch1->channels == 1)  // mono, single channel split to be two
              {
                out_buffer[ii] += (stoch1->split_now * amp
                        * (((double) *(stoch1->sound + stoch1->off1)) * stoch1->scale));
                out_buffer[ii+1] += ((1.0 - stoch1->split_now) * amp
                        * (((double) *(stoch1->sound + stoch1->off1)) * stoch1->scale));
              }
                  // if channels not 1 or 2, off1 out of synch with out_buffer[ii] and out_buffer[ii+1]
              stoch1->off1 += (stoch1->channels * fast_mult);  // adjust shorts played
              stoch1->split_now += (stoch1->split_adj * fast_mult);
                  // if channels not 1 or 2, play out of synch with out_buffer[ii] and out_buffer[ii+1]
              stoch1->play -= fast_mult;  // adjust frames played
            }
            stoch1->sofar += fast_mult;
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
                  /* frame start for next play  */
              sample1->off1 = (int_64) round ((drand48 ()) * sample1->frames);  // fine for mono
              if (sample1->channels == 2)  // offset is in shorts so have to double for stereo file
                sample1->off1 *= 2;  // this also fixes it so that offset is always left channel.
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
              double amp = sample1->amp * 2.;  // like binaural, double so each channel at amp with split
              if (sample1->channels == 2)  // stereo
              {
                if (sample1->mono == 0)  // stereo
                {
                  out_buffer[ii] += (sample1->split_now * amp
                          * (((double) *(sample1->sound + sample1->off1)) * sample1->scale));
                  out_buffer[ii+1] += ((1.0 - sample1->split_now) * amp
                          * (double) ((*(sample1->sound + sample1->off1 + 1)) * sample1->scale));
                }
                else if (sample1->mono == 1)  // mono in stereo form, left has sound, sample left as right channel
                {
                  out_buffer[ii] += (sample1->split_now * amp
                          * (((double) *(sample1->sound + sample1->off1)) * sample1->scale));
                  out_buffer[ii+1] += ((1.0 - sample1->split_now) * amp
                          * (((double) *(sample1->sound + sample1->off1)) * sample1->scale));
                }
                else if (sample1->mono == 2)  // mono in stereo form, right has sound, sample right as left channel
                {
                  out_buffer[ii] += (sample1->split_now * amp
                          * (((double) *(sample1->sound + sample1->off1 + 1)) * sample1->scale));
                  out_buffer[ii+1] += ((1.0 - sample1->split_now) * amp
                          * (((double) *(sample1->sound + sample1->off1 + 1)) * sample1->scale));
                }
              }
              else if (sample1->channels == 1)  // mono, single channel split to be two
              {
                out_buffer[ii] += (sample1->split_now * amp
                        * (((double) *(sample1->sound + sample1->off1)) * sample1->scale));
                out_buffer[ii+1] += ((1.0 - sample1->split_now) * amp
                        * (((double) *(sample1->sound + sample1->off1)) * sample1->scale));
              }
                  // if channels not 1 or 2, off1 out of synch with out_buffer[ii] and out_buffer[ii+1]
              sample1->off1 += (sample1->channels * fast_mult);
              sample1->off1 %= sample1->frames;  
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
              double amp = repeat1->amp * 2.;  // like binaural, double so each channel at amp with split
              if (repeat1->channels == 2)  // stereo
              {
                if (repeat1->mono == 0)  // stereo
                {
                  out_buffer[ii] += (repeat1->split_now * amp
                          * (((double) *(repeat1->sound + repeat1->off1)) * repeat1->scale));
                  out_buffer[ii+1] += ((1.0 - repeat1->split_now) * amp
                          * (double) ((*(repeat1->sound + repeat1->off1 + 1)) * repeat1->scale));
                }
                else if (repeat1->mono == 1)  // mono in stereo form, left has sound, repeat left as right channel
                {
                  out_buffer[ii] += (repeat1->split_now * amp
                          * (((double) *(repeat1->sound + repeat1->off1)) * repeat1->scale));
                  out_buffer[ii+1] += ((1.0 - repeat1->split_now) * amp
                          * (((double) *(repeat1->sound + repeat1->off1)) * repeat1->scale));
                }
                else if (repeat1->mono == 2)  // mono in stereo form, right has sound, repeat right as left channel
                {
                  out_buffer[ii] += (repeat1->split_now * amp
                          * (((double) *(repeat1->sound + repeat1->off1 + 1)) * repeat1->scale));
                  out_buffer[ii+1] += ((1.0 - repeat1->split_now) * amp
                          * (((double) *(repeat1->sound + repeat1->off1 + 1)) * repeat1->scale));
                }
              }
              else if (repeat1->channels == 1)  // mono, single channel split to be two
              {
                out_buffer[ii] += (repeat1->split_now * amp
                        * (((double) *(repeat1->sound + repeat1->off1)) * repeat1->scale));
                out_buffer[ii+1] += ((1.0 - repeat1->split_now) * amp
                        * (((double) *(repeat1->sound + repeat1->off1)) * repeat1->scale));
              }
                  // if channels not 1 or 2, off1 out of synch with out_buffer[ii] and out_buffer[ii+1]
              repeat1->off1 += (repeat1->channels * fast_mult); // adjust number of shorts played.
              repeat1->split_now += (repeat1->split_adj * fast_mult);
                  // if channels not 1 or 2, play out of synch with out_buffer[ii] and out_buffer[ii+1]
              repeat1->play -= fast_mult;  // adjust frames played
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
            if (once1->not_played && once1->sofar >= once1->play_when)
            {                     // time to play
              once1->not_played = 0;
              once1->off1 = 0;  // start at beginning of buffer
              once1->play = 0LL; // start play time at zero
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
                
              once1->split_adj = (split_end - once1->split_now) / once1->frames;  // adjust per frame
            }
            if (once1->sofar >= once1->play_when && once1->play < once1->frames)  // once is active
            {
              double amp = once1->amp * 2.;  // like binaural, double so each channel at amp with split
                // assumes only 1 or two channels, default to two if not one
              if (once1->channels == 2)  // stereo
              {
                if (once1->mono == 0)  // stereo
                {
                  out_buffer[ii] += (once1->split_now * amp
                          * (((double) *(once1->sound + once1->off1)) * once1->scale));
                  out_buffer[ii+1] += ((1.0 - once1->split_now) * amp
                          * (double) ((*(once1->sound + once1->off1 + 1)) * once1->scale));
                }
                else if (once1->mono == 1)  // mono in stereo form, left has sound, repeat left as right channel
                {
                  out_buffer[ii] += (once1->split_now * amp
                          * (((double) *(once1->sound + once1->off1)) * once1->scale));
                  out_buffer[ii+1] += ((1.0 - once1->split_now) * amp
                          * (((double) *(once1->sound + once1->off1)) * once1->scale));
                }
                else if (once1->mono == 2)  // mono in stereo form, right has sound, repeat right as left channel
                {
                  out_buffer[ii] += (once1->split_now * amp
                          * (((double) *(once1->sound + once1->off1 + 1)) * once1->scale));
                  out_buffer[ii+1] += ((1.0 - once1->split_now) * amp
                          * (((double) *(once1->sound + once1->off1 + 1)) * once1->scale));
                }
              }
              else if (once1->channels == 1)  // mono, single channel split to be two
              {
                out_buffer[ii] += (once1->split_now * amp
                        * (((double) *(once1->sound + once1->off1)) * once1->scale));
                out_buffer[ii+1] += ((1.0 - once1->split_now) * amp
                        * (((double) *(once1->sound + once1->off1)) * once1->scale));
              }
                  // if channels not 1 or 2, play out of synch with out_buffer[ii] and out_buffer[ii+1]
              once1->off1 += (once1->channels * fast_mult);  // short offset different depending on channels
              once1->split_now += (once1->split_adj * fast_mult);
                  // if channels not 1 or 2, play out of synch with out_buffer[ii] and out_buffer[ii+1]
              once1->play += fast_mult;  // add frames just played to the total played, offset into sound buffer
            }
            once1->sofar += fast_mult;
          }
        }
        break;
      case 8:                // Chronaural tones
        {
          double sinval, sinval2;
          double freq1, freq2;
          double amp1;
          chronaural *chronaural1;

          chronaural1 = (chronaural *) this;  // reassign void pointer as chronaural struct

          if (chronaural1->first_pass)
          {
            chronaural1->first_pass = 0;  // now active
            chronaural1->fade_factor = 1.0; // set fade to start play
            chronaural1->fade_factor2 = 1.0; // set fade to start play
            chronaural1->fade_sinval = -2.0;  // negative value as flag to start play
            chronaural1->fade_sinval2 = -2.0;  // negative value as flag to start play
            if (chronaural1->last_off1 != NULL)  // there *is* a previous offset to use
              chronaural1->off1 = *chronaural1->last_off1;  // to eliminate crackle from discontinuity in wave
            if (chronaural1->last_off3 != NULL)  // there *is* a previous offset to use
              chronaural1->off3 = *chronaural1->last_off3;  // to eliminate crackle from discontinuity in wave
            if (chronaural1->last_off2 != NULL)  // there *is* a previous offset to use
              chronaural1->off2 = *chronaural1->last_off2;
          }
          for (ii= channels * offset; ii < channels * frame_count; ii+= channels)
          {
            chronaural1->inc2 += (fabs(chronaural1->beat) * 2. * fast_mult);  //inc to next sin value, allow for -ve beat
            chronaural1->off2 += (int) round(chronaural1->inc2);  // offset for beat frequency into sin table
            chronaural1->inc2 -= round (chronaural1->inc2);  // remaining increment is only fractional part, +ve or -ve
            chronaural1->off2 = chronaural1->off2 % sin_siz;  // mod to wrap offset
            int shift = (int) ((chronaural1->phase/360.) * sin_siz);  // offset shift for phase
            sinval = sin_table [chronaural1->off2];  // sin val at current beat point
            sinval2 = sin_table [(chronaural1->off2 + shift) % sin_siz];  // sin val at current beat point plus shift
            /*  check the unshifted beat to see if it is time to play, play the unshifted channel if necessary */
            if (sinval >= 0.0 && sinval >= chronaural1->sin_threshold)  // time to play, only on positive sine
            {
              freq1 = chronaural1->carrier;
              /* Set up a fade out to stop click at end.  None at beginning, always begin at 0 */
              if (chronaural1->fade_sinval == -2.0)  // start of beat play
              { /* set sin value at which to start fade out */
                chronaural1->fade_sinval = chronaural1->sin_threshold;  
              }
            }
            else if (chronaural1->fade_sinval != -2.0 && sinval < chronaural1->fade_sinval)  // fade out begins on way down
            {
              if (chronaural1->fade_factor > 0.0)  // less than millisecond fade
              {
                freq1 = chronaural1->carrier;
                chronaural1->fade_factor -= msec_fade_adjust; // adjust fade factor down
              }
              else
              { /* chronaural beat has ended for this pass, make sure ready for start of next beat play */
                freq1 = 0.0;  // don't play beat
                chronaural1->off1 = 0;  // always start at zero to eliminate beginning discontinuity
                chronaural1->fade_factor = 1.0; // set start fade factor to full volume
                chronaural1->fade_sinval = -2.0;  // negative value as flag for start of beat play
              }
            }
            else  // no beat is playing
              freq1 = 0.0;
            if (freq1 != 0.0)
            {
              if (opt_c)  // compensate
              {
                amp1 = (chronaural1->amp * amp_comp (freq1));
              }
              else
                amp1 = chronaural1->amp;
              amp1 *= 2.;  // like binaural, double so each channel at amp with split
              if (chronaural1->beat_behave == 1)  // sin wave, adjust by sin value
              {
                if (chronaural1->beat > 0.0)  // left channel no phase shift
                  out_buffer[ii] += (chronaural1->split_now * sinval * amp1 * chronaural1->fade_factor
                                                          * sin_table[chronaural1->off1]);
                else if (chronaural1->beat < 0.0)  // right channel no phase shift
                  out_buffer[ii+1] += ((1.0 - chronaural1->split_now) * sinval * amp1 * chronaural1->fade_factor
                                                          * sin_table[chronaural1->off1]);
              }
              else if (chronaural1->beat_behave == 2)      // square wave, full volume
              {
                if (chronaural1->beat > 0.0)  // left channel no phase shift
                  out_buffer[ii] += (chronaural1->split_now * amp1 * chronaural1->fade_factor
                                                          * sin_table[chronaural1->off1]);
                else if (chronaural1->beat < 0.0)  // right channel no phase shift
                  out_buffer[ii+1] += ((1.0 - chronaural1->split_now) * amp1 * chronaural1->fade_factor
                                                          * sin_table[chronaural1->off1]);
              }
              else if (chronaural1->beat_behave == 3)  // dirac delta approximation
              {
                double filter = pow(sinval, 5.); // quint the sin to make pseudo dirac
                if (chronaural1->beat > 0.0)  // left channel no phase shift
                  out_buffer[ii] += (chronaural1->split_now * filter * amp1 * chronaural1->fade_factor
                                                          * sin_table[chronaural1->off1]);
                else if (chronaural1->beat < 0.0)  // right channel no phase shift
                  out_buffer[ii+1] += ((1.0 - chronaural1->split_now) * filter * amp1 * chronaural1->fade_factor
                                                          * sin_table[chronaural1->off1]);
              }
              else if (chronaural1->beat_behave == 4)  // extreme dirac delta approximation
              {
                double filter = pow(sinval, 15.); // 15th power of the sin to make extreme pseudo dirac
                if (chronaural1->beat > 0.0)  // left channel no phase shift
                  out_buffer[ii] += (chronaural1->split_now * filter * amp1 * chronaural1->fade_factor
                                                          * sin_table[chronaural1->off1]);
                else if (chronaural1->beat < 0.0)  // right channel no phase shift
                  out_buffer[ii+1] += ((1.0 - chronaural1->split_now) * filter * amp1 * chronaural1->fade_factor
                                                          * sin_table[chronaural1->off1]);
              }
              /* always start at zero, adjust at the end of pass so the zero not incremented on first pass */
              chronaural1->inc1 = (int) round(freq1*2);  // (freq1 / out_rate) * (out_rate * 2));
              chronaural1->off1 += chronaural1->inc1;
              chronaural1->off1 = chronaural1->off1 % sin_siz;
            }
            /*  check the phase shifted beat to see if it is time to play, play the shifted channel if necessary */
            if (sinval2 >= 0.0 && sinval2 >= chronaural1->sin_threshold)  // time to play, only on positive sine
            {
              freq2 = chronaural1->carrier;
              /* Set up a fade out to stop click at end.  None at beginning, always begin at 0 */
              if (chronaural1->fade_sinval2 == -2.0)  // start of beat play
              { /* set sin value at which to start fade out */
                chronaural1->fade_sinval2 = chronaural1->sin_threshold;  
              }
            }
            else if (chronaural1->fade_sinval2 != -2.0 && sinval2 < chronaural1->fade_sinval2)  // fade out begins on way down
            {
              if (chronaural1->fade_factor2 > 0.0)  // less than millisecond fade
              {
                freq2 = chronaural1->carrier;
                chronaural1->fade_factor2 -= msec_fade_adjust; // adjust fade factor down
              }
              else
              { /* chronaural beat has ended for this pass, make sure ready for start of next beat play */
                freq2 = 0.0;  // don't play beat
                chronaural1->off3 = 0;  // always start at zero to eliminate beginning discontinuity
                chronaural1->fade_factor2 = 1.0; // set start fade factor to full volume
                chronaural1->fade_sinval2 = -2.0;  // negative value as flag for start of beat play
              }
            }
            else  // no beat is playing
              freq2 = 0.0;
            if (freq2 != 0.0)
            {
              if (opt_c)  // compensate
              {
                amp1 = (chronaural1->amp * amp_comp (freq2));
              }
              else
                amp1 = chronaural1->amp;
              if (chronaural1->beat_behave == 1)  // sin wave, adjust by sin value
              {
                if (chronaural1->beat < 0.0)  // left channel no phase shift
                  out_buffer[ii] += (chronaural1->split_now * sinval2 * amp1 * chronaural1->fade_factor2
                                                          * sin_table[chronaural1->off3]);
                else if (chronaural1->beat > 0.0)  // right channel no phase shift
                  out_buffer[ii+1] += ((1.0 - chronaural1->split_now) * sinval2 * amp1 * chronaural1->fade_factor2
                                                          * sin_table[chronaural1->off3]);
              }
              else if (chronaural1->beat_behave == 2)      // square wave, full volume
              {
                if (chronaural1->beat < 0.0)  // left channel no phase shift
                  out_buffer[ii] += (chronaural1->split_now * amp1 * chronaural1->fade_factor2
                                                          * sin_table[chronaural1->off3]);
                else if (chronaural1->beat > 0.0)  // right channel no phase shift
                  out_buffer[ii+1] += ((1.0 - chronaural1->split_now) * amp1 * chronaural1->fade_factor2
                                                          * sin_table[chronaural1->off3]);
              }
              else if (chronaural1->beat_behave == 3)  // dirac delta approximation
              {
                double filter = pow(sinval2, 5.); // quint the sin to make pseudo dirac
                if (chronaural1->beat < 0.0)  // left channel no phase shift
                  out_buffer[ii] += (chronaural1->split_now * filter * amp1 * chronaural1->fade_factor2
                                                          * sin_table[chronaural1->off3]);
                else if (chronaural1->beat > 0.0)  // right channel no phase shift
                  out_buffer[ii+1] += ((1.0 - chronaural1->split_now) * filter * amp1 * chronaural1->fade_factor2
                                                          * sin_table[chronaural1->off3]);
              }
              else if (chronaural1->beat_behave == 4)  // extreme dirac delta approximation
              {
                double filter = pow(sinval2, 15.); // 15th power of the sin to make extreme pseudo dirac
                if (chronaural1->beat < 0.0)  // left channel no phase shift
                  out_buffer[ii] += (chronaural1->split_now * filter * amp1 * chronaural1->fade_factor2
                                                          * sin_table[chronaural1->off3]);
                else if (chronaural1->beat > 0.0)  // right channel no phase shift
                  out_buffer[ii+1] += ((1.0 - chronaural1->split_now) * filter * amp1 * chronaural1->fade_factor2
                                                          * sin_table[chronaural1->off3]);
              }
              /* always start at zero, adjust at the end of pass so the zero not incremented on first pass */
              chronaural1->inc3 = (int) round(freq2*2);  // (freq2 / out_rate) * (out_rate * 2));
              chronaural1->off3 += chronaural1->inc3;
              chronaural1->off3 = chronaural1->off3 % sin_siz;
            }
            /*  Adjust split or split beat even when not playing beat */
            chronaural1->split_now += chronaural1->split_adj * fast_mult;
            if (chronaural1->split_beat == 0.0 && chronaural1->split_beat_adj == 0.0)
            {  // no split beat adjust, adjust split towards split_end
              if (chronaural1->split_now < 0.0)
                chronaural1->split_now = 0.0;
              else if (chronaural1->split_now > 1.0)
                chronaural1->split_now = 1.0;
            }
            else // split beat so oscillates between begin and end
            {
              double split_dist = fabs (chronaural1->split_end - chronaural1->split_begin);
                /* assumes split_end > split_begin, this is done in finish_beat_voice_setup */
              if (chronaural1->split_now >= chronaural1->split_end)  // larger than end
              {
                double delta = fabs (chronaural1->split_now - chronaural1->split_end);  // overshoot
                if (delta > split_dist) // overshoot too large, set to end
                  chronaural1->split_now = chronaural1->split_end;
                else // overshoot smaller than overall split, reflect from end
                  chronaural1->split_now = chronaural1->split_end - delta;
                chronaural1->split_adj *= -1.;  // swap direction
              }
              else if (chronaural1->split_now <= chronaural1->split_begin)  // smaller than begin
              {
                double delta = fabs (chronaural1->split_begin - chronaural1->split_now);  // overshoot
                if (delta > split_dist) // overshoot too large, set to begin
                  chronaural1->split_now = chronaural1->split_begin;
                else // overshoot smaller than overall split, reflect from begin
                  chronaural1->split_now = chronaural1->split_begin + delta;
                chronaural1->split_adj *= -1.;  // swap direction
              }
              /* Adjust the split beat and split adjust.  Second difference equation. */
              chronaural1->split_beat += (chronaural1->split_beat_adj * fast_mult);
              double sign_adjust = 1.0;  // default to positive when split_adj == 0.0
              if (chronaural1->split_adj != 0.0)
                sign_adjust = fabs(chronaural1->split_adj) / chronaural1->split_adj;
              chronaural1->split_adj = fabs(chronaural1->split_adj) 
                                            + (chronaural1->split_beat_adj * (2.* split_dist) / (double) out_rate);  
              chronaural1->split_adj *= sign_adjust;
            }  
            chronaural1->carrier += (chronaural1->carr_adj * fast_mult);  // tone to sound if time
            chronaural1->beat += (chronaural1->beat_adj * fast_mult);  // beat of the amplitude
            chronaural1->phase += (chronaural1->phase_adj * fast_mult);  // phase of the amplitude
            chronaural1->amp += (chronaural1->amp_adj * fast_mult);  // amplitude to sound at
            if (chronaural1->amp < 0.0)  // no negative amplitudes
              chronaural1->amp = 0.0;
          }
        }
        break;
      case 9:                // Binaural tone, step slide, little less efficient, two extra checks each pass
      case 11:                // Binaural tone, vary slide, little less efficient, two extra checks each pass
        {
          double freq1, freq2;
          double amp1, amp2;
          binaural *binaural1;

          binaural1 = (binaural *) this;  // reassign void pointer as binaural struct
          for (ii= channels * offset; ii < channels * frame_count; ii+= channels)
          {
            if (binaural1->cur_frames >= binaural1->tot_frames)  // step voice finished
            {
              binaural *binaural2;
              binaural2 = binaural1->step_next;
              binaural2->next = binaural1->next;
              binaural2->prev = binaural1->prev;
              if (binaural1->prev != NULL)
                ((binaural *) binaural1->prev)->next = binaural2;
              else  // must be first voice in chain for time sequence
                snd1->voices = (void *) binaural2;
              if (binaural1->next != NULL)
                ((binaural *) binaural1->next)->prev = binaural2;
              /* free(binaural1); */  // not bothering to free, because it could slow down sound generation
              binaural1 = binaural2;  // new voice from step list
            }

            /* if start of the voice, set starting offset to be last offset of previous voice */
            if (binaural1->first_pass)
            {
              binaural1->first_pass = 0;  // now active
              if (binaural1->last_off1 != NULL)  // there *is* a previous offset to use
                binaural1->off1 = *binaural1->last_off1;  // to eliminate crackle from discontinuity in wave
              if (binaural1->last_off2 != NULL)  // there *is* a previous offset to use
                binaural1->off2 = *binaural1->last_off2;
              if (binaural1->last_amp_off1 != NULL)  // there *is* a previous amp_offset to use
                binaural1->amp_off1 = *binaural1->last_amp_off1;  // to eliminate crackle from discontinuity in wave
              if (binaural1->last_amp_off2 != NULL)  // there *is* a previous amp_offset to use
                binaural1->amp_off2 = *binaural1->last_amp_off2;
            }
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
              binaural1->beat += (binaural1->beat_adj * fast_mult);
              binaural1->amp += (binaural1->amp_adj * fast_mult);
              binaural1->amp_beat1 += (binaural1->amp_beat1_adj * fast_mult);
              binaural1->amp_beat2 += (binaural1->amp_beat2_adj * fast_mult);
              binaural1->amp_pct1 += (binaural1->amp_pct1_adj * fast_mult);
              binaural1->amp_pct2 += (binaural1->amp_pct2_adj * fast_mult);
            }
            binaural1->cur_frames += 1 * fast_mult;  
          }
        }
        break;
      case 10:                // Chronaural tones step slide
      case 12:                // Chronaural tones vary slide
        {
          double sinval, sinval2;
          double freq1, freq2;
          double amp1;
          chronaural *chronaural1;

          chronaural1 = (chronaural *) this;  // reassign void pointer as chronaural struct

          for (ii= channels * offset; ii < channels * frame_count; ii+= channels)
          {
            if (chronaural1->cur_frames >= chronaural1->tot_frames)  // step voice finished
            {
              chronaural *chronaural2;
              chronaural2 = chronaural1->step_next;
              chronaural2->next = chronaural1->next;
              chronaural2->prev = chronaural1->prev;
              if (chronaural1->prev != NULL)
                ((chronaural *) chronaural1->prev)->next = chronaural2;
              else  // must be first voice in chain for time sequence
                snd1->voices = (void *) chronaural2;
              if (chronaural1->next != NULL)
                ((chronaural *) chronaural1->next)->prev = chronaural2;
              /* free(chronaural1); */  // not bothering to free, because it could slow down sound generation
              chronaural1 = chronaural2;  // new voice from step list
            }
            if (chronaural1->first_pass)
            {
              chronaural1->first_pass = 0;  // now active
              chronaural1->fade_factor = 1.0; // set fade to start play
              chronaural1->fade_factor2 = 1.0; // set fade to start play
              chronaural1->fade_sinval = -2.0;  // negative value as flag to start play
              chronaural1->fade_sinval2 = -2.0;  // negative value as flag to start play
              if (chronaural1->last_off1 != NULL)  // there *is* a previous offset to use
                chronaural1->off1 = *chronaural1->last_off1;  // to eliminate crackle from discontinuity in wave
              if (chronaural1->last_off3 != NULL)  // there *is* a previous offset to use
                chronaural1->off3 = *chronaural1->last_off3;  // to eliminate crackle from discontinuity in wave
              if (chronaural1->last_off2 != NULL)  // there *is* a previous offset to use
                chronaural1->off2 = *chronaural1->last_off2;
            }
            chronaural1->inc2 += (fabs(chronaural1->beat) * 2. * fast_mult);  //inc to next sin value, allow for -ve beat
            chronaural1->off2 += (int) round(chronaural1->inc2);  // offset for beat frequency into sin table
            chronaural1->inc2 -= round (chronaural1->inc2);  // remaining increment is only fractional part, +ve or -ve
            chronaural1->off2 = chronaural1->off2 % sin_siz;  // mod to wrap offset
            int shift = (int) ((chronaural1->phase/360.) * sin_siz);  // offset shift for phase
            sinval = sin_table [chronaural1->off2];  // sin val at current beat point
            sinval2 = sin_table [(chronaural1->off2 + shift) % sin_siz];  // sin val at current beat point plus shift
            /*  check the unshifted beat to see if it is time to play, play the unshifted channel if necessary */
            if (sinval >= 0.0 && sinval >= chronaural1->sin_threshold)  // time to play, only on positive sine
            {
              freq1 = chronaural1->carrier;
              /* Set up a fade out to stop click at end.  None at beginning, always begin at 0 */
              if (chronaural1->fade_sinval == -2.0)  // start of beat play
              { /* set sin value at which to start fade out */
                chronaural1->fade_sinval = chronaural1->sin_threshold;  
              }
            }
            else if (chronaural1->fade_sinval != -2.0 && sinval < chronaural1->fade_sinval)  // fade out begins on way down
            {
              if (chronaural1->fade_factor > 0.0)  // less than millisecond fade
              {
                freq1 = chronaural1->carrier;
                chronaural1->fade_factor -= msec_fade_adjust; // adjust fade factor down
              }
              else
              { /* chronaural beat has ended for this pass, make sure ready for start of next beat play */
                freq1 = 0.0;  // don't play beat
                chronaural1->off1 = 0;  // always start at zero to eliminate beginning discontinuity
                chronaural1->fade_factor = 1.0; // set start fade factor to full volume
                chronaural1->fade_sinval = -2.0;  // negative value as flag for start of beat play
              }
            }
            else  // no beat is playing
              freq1 = 0.0;
            if (freq1 != 0.0)
            {
              if (opt_c)  // compensate
              {
                amp1 = (chronaural1->amp * amp_comp (freq1));
              }
              else
                amp1 = chronaural1->amp;
              amp1 *= 2.;  // like binaural, double so each channel at amp with split
              if (chronaural1->beat_behave == 1)  // sin wave, adjust by sin value
              {
                if (chronaural1->beat > 0.0)  // left channel no phase shift
                  out_buffer[ii] += (chronaural1->split_now * sinval * amp1 * chronaural1->fade_factor
                                                          * sin_table[chronaural1->off1]);
                else if (chronaural1->beat < 0.0)  // right channel no phase shift
                  out_buffer[ii+1] += ((1.0 - chronaural1->split_now) * sinval * amp1 * chronaural1->fade_factor
                                                          * sin_table[chronaural1->off1]);
              }
              else if (chronaural1->beat_behave == 2)      // square wave, full volume
              {
                if (chronaural1->beat > 0.0)  // left channel no phase shift
                  out_buffer[ii] += (chronaural1->split_now * amp1 * chronaural1->fade_factor
                                                          * sin_table[chronaural1->off1]);
                else if (chronaural1->beat < 0.0)  // right channel no phase shift
                  out_buffer[ii+1] += ((1.0 - chronaural1->split_now) * amp1 * chronaural1->fade_factor
                                                          * sin_table[chronaural1->off1]);
              }
              else if (chronaural1->beat_behave == 3)  // dirac delta approximation
              {
                double filter = pow(sinval, 5.); // quint the sin to make pseudo dirac
                if (chronaural1->beat > 0.0)  // left channel no phase shift
                  out_buffer[ii] += (chronaural1->split_now * filter * amp1 * chronaural1->fade_factor
                                                          * sin_table[chronaural1->off1]);
                else if (chronaural1->beat < 0.0)  // right channel no phase shift
                  out_buffer[ii+1] += ((1.0 - chronaural1->split_now) * filter * amp1 * chronaural1->fade_factor
                                                          * sin_table[chronaural1->off1]);
              }
              else if (chronaural1->beat_behave == 4)  // extreme dirac delta approximation
              {
                double filter = pow(sinval, 15.); // 15th power of the sin to make extreme pseudo dirac
                if (chronaural1->beat > 0.0)  // left channel no phase shift
                  out_buffer[ii] += (chronaural1->split_now * filter * amp1 * chronaural1->fade_factor
                                                          * sin_table[chronaural1->off1]);
                else if (chronaural1->beat < 0.0)  // right channel no phase shift
                  out_buffer[ii+1] += ((1.0 - chronaural1->split_now) * filter * amp1 * chronaural1->fade_factor
                                                          * sin_table[chronaural1->off1]);
              }
              /* always start at zero, adjust at the end of pass so the zero not incremented on first pass */
              chronaural1->inc1 = (int) round(freq1*2);  // (freq1 / out_rate) * (out_rate * 2));
              chronaural1->off1 += chronaural1->inc1;
              chronaural1->off1 = chronaural1->off1 % sin_siz;
            }
            /*  check the phase shifted beat to see if it is time to play, play the shifted channel if necessary */
            if (sinval2 >= 0.0 && sinval2 >= chronaural1->sin_threshold)  // time to play, only on positive sine
            {
              freq2 = chronaural1->carrier;
              /* Set up a fade out to stop click at end.  None at beginning, always begin at 0 */
              if (chronaural1->fade_sinval2 == -2.0)  // start of beat play
              { /* set sin value at which to start fade out */
                chronaural1->fade_sinval2 = chronaural1->sin_threshold;  
              }
            }
            else if (chronaural1->fade_sinval2 != -2.0 && sinval2 < chronaural1->fade_sinval2)  // fade out begins on way down
            {
              if (chronaural1->fade_factor2 > 0.0)  // less than millisecond fade
              {
                freq2 = chronaural1->carrier;
                chronaural1->fade_factor2 -= msec_fade_adjust; // adjust fade factor down
              }
              else
              { /* chronaural beat has ended for this pass, make sure ready for start of next beat play */
                freq2 = 0.0;  // don't play beat
                chronaural1->off3 = 0;  // always start at zero to eliminate beginning discontinuity
                chronaural1->fade_factor2 = 1.0; // set start fade factor to full volume
                chronaural1->fade_sinval2 = -2.0;  // negative value as flag for start of beat play
              }
            }
            else  // no beat is playing
              freq2 = 0.0;
            if (freq2 != 0.0)
            {
              if (opt_c)  // compensate
              {
                amp1 = (chronaural1->amp * amp_comp (freq2));
              }
              else
                amp1 = chronaural1->amp;
              amp1 *= 2.;  // like binaural, double so each channel at amp with split
              if (chronaural1->beat_behave == 1)  // sin wave, adjust by sin value
              {
                if (chronaural1->beat < 0.0)  // left channel no phase shift
                  out_buffer[ii] += (chronaural1->split_now * sinval2 * amp1 * chronaural1->fade_factor2
                                                          * sin_table[chronaural1->off3]);
                else if (chronaural1->beat > 0.0)  // right channel no phase shift
                  out_buffer[ii+1] += ((1.0 - chronaural1->split_now) * sinval2 * amp1 * chronaural1->fade_factor2
                                                          * sin_table[chronaural1->off3]);
              }
              else if (chronaural1->beat_behave == 2)      // square wave, full volume
              {
                if (chronaural1->beat < 0.0)  // left channel no phase shift
                  out_buffer[ii] += (chronaural1->split_now * amp1 * chronaural1->fade_factor2
                                                          * sin_table[chronaural1->off3]);
                else if (chronaural1->beat > 0.0)  // right channel no phase shift
                  out_buffer[ii+1] += ((1.0 - chronaural1->split_now) * amp1 * chronaural1->fade_factor2
                                                          * sin_table[chronaural1->off3]);
              }
              else if (chronaural1->beat_behave == 3)  // dirac delta approximation
              {
                double filter = pow(sinval2, 5.); // quint the sin to make pseudo dirac
                if (chronaural1->beat < 0.0)  // left channel no phase shift
                  out_buffer[ii] += (chronaural1->split_now * filter * amp1 * chronaural1->fade_factor2
                                                          * sin_table[chronaural1->off3]);
                else if (chronaural1->beat > 0.0)  // right channel no phase shift
                  out_buffer[ii+1] += ((1.0 - chronaural1->split_now) * filter * amp1 * chronaural1->fade_factor2
                                                          * sin_table[chronaural1->off3]);
              }
              else if (chronaural1->beat_behave == 4)  // extreme dirac delta approximation
              {
                double filter = pow(sinval2, 15.); // 15th power of the sin to make extreme pseudo dirac
                if (chronaural1->beat < 0.0)  // left channel no phase shift
                  out_buffer[ii] += (chronaural1->split_now * filter * amp1 * chronaural1->fade_factor2
                                                          * sin_table[chronaural1->off3]);
                else if (chronaural1->beat > 0.0)  // right channel no phase shift
                  out_buffer[ii+1] += ((1.0 - chronaural1->split_now) * filter * amp1 * chronaural1->fade_factor2
                                                          * sin_table[chronaural1->off3]);
              }
              /* always start at zero, adjust at the end of pass so the zero not incremented on first pass */
              chronaural1->inc3 = (int) round(freq2*2);  // (freq2 / out_rate) * (out_rate * 2));
              chronaural1->off3 += chronaural1->inc3;
              chronaural1->off3 = chronaural1->off3 % sin_siz;
            }
            /*  Adjust split or split beat even when not playing beat */
            chronaural1->split_now += chronaural1->split_adj * fast_mult;
            if (chronaural1->split_beat == 0.0)  // no split beat, adjust split towards split_end
            {
              if (chronaural1->split_now < 0.0)
                chronaural1->split_now = 0.0;
              else if (chronaural1->split_now > 1.0)
                chronaural1->split_now = 1.0;
            }
            else // split beat so oscillates between begin and end
            {
              double split_dist = fabs (chronaural1->split_end - chronaural1->split_begin);
                /* assumes split_end > split_begin, this is done in finish_beat_voice_setup */
              if (chronaural1->split_now > chronaural1->split_end)  // larger than end
              {
                double delta = fabs (chronaural1->split_now - chronaural1->split_end);  // overshoot
                if (delta > split_dist) // overshoot too large, set to end
                  chronaural1->split_now = chronaural1->split_end;
                else // overshoot smaller than overall split, reflect from end
                  chronaural1->split_now = chronaural1->split_end - delta;
                chronaural1->split_adj *= -1.;  // swap direction
              }
              else if (chronaural1->split_now < chronaural1->split_begin)  // smaller than begin
              {
                double delta = fabs (chronaural1->split_begin - chronaural1->split_now);  // overshoot
                if (delta > split_dist) // overshoot too large, set to begin
                  chronaural1->split_now = chronaural1->split_begin;
                else // overshoot smaller than overall split, reflect from begin
                  chronaural1->split_now = chronaural1->split_begin + delta;
                chronaural1->split_adj *= -1.;  // swap direction
              }
              /* Adjust the split beat and split adjust.  Second difference equation. */
              chronaural1->split_beat += (chronaural1->split_beat_adj * fast_mult);
              double sign_adjust = 1.0;  // default to positive when split_adj == 0.0
              if (chronaural1->split_adj != 0.0)
                sign_adjust = fabs(chronaural1->split_adj) / chronaural1->split_adj;
              chronaural1->split_adj = fabs(chronaural1->split_adj) 
                                            + ((chronaural1->split_beat_adj * (2. * split_dist)) / (double) out_rate);  
              chronaural1->split_adj *= sign_adjust;
            }  
            chronaural1->carrier += (chronaural1->carr_adj * fast_mult);  // tone to sound if time
            chronaural1->beat += (chronaural1->beat_adj * fast_mult);  // beat of the amplitude
            chronaural1->phase += (chronaural1->phase_adj * fast_mult);  // phase of the amplitude
            chronaural1->amp += (chronaural1->amp_adj * fast_mult);  // amplitude to sound at
            if (chronaural1->amp < 0.0)  // no negative amplitudes
              chronaural1->amp = 0.0;
            chronaural1->cur_frames += 1 * fast_mult;  
          }
        }
        break;
      case 13:                // Pulse tones
        {
          double amp1;
          int off2_prev;
          pulse *pulse1;

          pulse1 = (pulse *) this;  // reassign void pointer as pulse struct

          if (pulse1->first_pass)
          {
            pulse1->first_pass = 0;  // now active
            pulse1->fade_factor_left = 1.0; // set fade for left channel to start play
            pulse1->fade_factor_right = 1.0; // set fade for right channel to start play
            if (pulse1->last_off1 != NULL)  // there *is* a previous offset to use
              pulse1->off1 = *pulse1->last_off1;  // to eliminate crackle from discontinuity in wave
            if (pulse1->last_off3 != NULL)  // there *is* a previous offset to use
              pulse1->off3 = *pulse1->last_off3;  // to eliminate crackle from discontinuity in wave
            if (pulse1->last_off2 != NULL)  // there *is* a previous offset to use
              pulse1->off2 = *pulse1->last_off2;
          }
          for (ii= channels * offset; ii < channels * frame_count; ii+= channels)  // fill buffer 
          {
            off2_prev = pulse1->off2;  // save the original offset to determine if time to play pulse
            pulse1->inc2 += (fabs(pulse1->beat) * 2. * fast_mult);  //inc to next sin value, allow for -ve beat
            pulse1->off2 += (int) round(pulse1->inc2);  // offset for beat frequency into sin table
            pulse1->inc2 -= round (pulse1->inc2);  // remaining increment is only fractional part, +ve or -ve
            pulse1->off2 = pulse1->off2 % sin_siz;  // mod with sin table size, to wrap offset
            int shift = (int) ((pulse1->phase/360.) * sin_siz);  // offset shift for phase
            if (pulse1->beat < 0.0)  // left channel leads
            {
              if (off2_prev > pulse1->off2)  // time to play left channel, beat offset just wrapped to start of sin table
                pulse1->frames_left = (int) (pulse1->time * out_rate);  // number of frames to play
              /* time to play right channel, shifted beat offset just wrapped to start of sin table */
              if ((off2_prev + shift) % sin_siz > (pulse1->off2 + shift) % sin_siz)
                pulse1->frames_right = (int) (pulse1->time * out_rate);  // number of frames to play
              /* fade out begins one millisecond from end  */
              if (pulse1->frames_left > 0 && pulse1->frames_left <= msec_fade_count)  
                pulse1->fade_factor_left -= (msec_fade_adjust * fast_mult); // adjust fade factor down
              if (pulse1->frames_right > 0 && pulse1->frames_right <= msec_fade_count)  
                pulse1->fade_factor_right -= (msec_fade_adjust * fast_mult); // adjust fade factor down
              if (pulse1->frames_left <= 0 && pulse1->frames_left > -fast_mult)  // have to allow for fast play
              { /* left pulse beat has ended for this pass, make sure ready for start of next beat play on left */
                pulse1->off1 = 0;  // always start at zero to eliminate beginning discontinuity
                pulse1->fade_factor_left = 1.0; // set start fade factor to full volume
              }
              if (pulse1->frames_right <= 0 && pulse1->frames_right > -fast_mult)  // have to allow for fast play
              { /* right pulse beat has ended for this pass, make sure ready for start of next beat play on right */
                pulse1->off3 = 0;  // always start at zero to eliminate beginning discontinuity
                pulse1->fade_factor_right = 1.0; // set start fade factor to full volume
              }
            }
            else if (pulse1->beat > 0.0)  // right channel leads
            {
              /* time to play left channel, shifted beat offset just wrapped to start of sin table */
              if ((off2_prev + shift) % sin_siz > (pulse1->off2 + shift) % sin_siz)
                pulse1->frames_left = (int) (pulse1->time * out_rate);  // number of frames to play
              if (off2_prev > pulse1->off2)  // time to play right channel, beat offset just wrapped to start of sin table
                pulse1->frames_right = (int) (pulse1->time * out_rate);  // number of frames to play
              /* fade out begins one millisecond from end  */
              if (pulse1->frames_left > 0 && pulse1->frames_left <= msec_fade_count)  
                pulse1->fade_factor_left -= (msec_fade_adjust * fast_mult); // adjust fade factor down
              if (pulse1->frames_right > 0 && pulse1->frames_right <= msec_fade_count)  
                pulse1->fade_factor_right -= (msec_fade_adjust * fast_mult); // adjust fade factor down
              if (pulse1->frames_left <= 0 && pulse1->frames_left > -fast_mult)  // have to allow for fast play
              { /* left pulse beat has ended for this pass, make sure ready for start of next beat play on left */
                pulse1->off1 = 0;  // always start at zero to eliminate beginning discontinuity
                pulse1->fade_factor_left = 1.0; // set start fade factor to full volume
              }
              if (pulse1->frames_right <= 0 && pulse1->frames_right > -fast_mult)  // have to allow for fast play
              { /* right pulse beat has ended for this pass, make sure ready for start of next beat play on right */
                pulse1->off3 = 0;  // always start at zero to eliminate beginning discontinuity
                pulse1->fade_factor_right = 1.0; // set start fade factor to full volume
              }
            }
            else  // in phase
            {
              if (off2_prev > pulse1->off2)  // time to play, beat offset just wrapped to start of sin table
              {
                pulse1->frames_left = (int) (pulse1->time * out_rate);  // number of frames to play
                pulse1->frames_right = (int) (pulse1->time * out_rate);  // number of frames to play
              }
              /* fade out begins one millisecond from end  */
              if (pulse1->frames_left > 0 && pulse1->frames_left <= msec_fade_count) 
              {
                pulse1->fade_factor_left -= (msec_fade_adjust * fast_mult); // adjust fade factor down
                pulse1->fade_factor_right -= (msec_fade_adjust * fast_mult); // adjust fade factor down
              }
              if (pulse1->frames_left <= 0 && pulse1->frames_left > -fast_mult)  // have to allow for fast play
              { /* pulse beat has ended for this pass, make sure ready for start of next beat play */
                pulse1->off1 = 0;  // always start at zero to eliminate beginning discontinuity
                pulse1->fade_factor_left = 1.0; // set start fade factor to full volume
                pulse1->off3 = 0;  // always start at zero to eliminate beginning discontinuity
                pulse1->fade_factor_right = 1.0; // set start fade factor to full volume
              }
            }
            if (pulse1->frames_left > 0)  // playing a pulse in left channel
            {
              if (opt_c)  // compensate
                amp1 = (pulse1->amp * amp_comp (pulse1->carrier));
              else
                amp1 = pulse1->amp;
              amp1 *= 2.;  // like binaural, double so each channel at amp with split
              /* pulse is always square wave, full volume  */
              out_buffer[ii] += (pulse1->split_now * amp1 * pulse1->fade_factor_left
                                                        * sin_table[pulse1->off1]);
              /* always start at zero, adjust at the end of pass so the zero not incremented on first pass */
              pulse1->inc1 = (int) round(pulse1->carrier * 2 * fast_mult);  // (freq1 / out_rate) * (out_rate * 2));
              pulse1->off1 += pulse1->inc1;  // don't worry about fractional portion, frequency high enough to ignore
              pulse1->off1 = pulse1->off1 % sin_siz;  // mod with sin table size, to wrap offset
            }
            if (pulse1->frames_right > 0)  // playing a pulse in right channel
            {
              if (opt_c)  // compensate
                amp1 = (pulse1->amp * amp_comp (pulse1->carrier));
              else
                amp1 = pulse1->amp;
              amp1 *= 2.;  // like binaural, double so each channel at amp with split
              /* pulse is always square wave, full volume  */
              out_buffer[ii+1] += ((1.0 - pulse1->split_now) * amp1 * pulse1->fade_factor_right
                                                        * sin_table[pulse1->off3]);
              /* always start at zero, adjust at the end of pass so the zero not incremented on first pass */
              pulse1->inc3 = (int) round(pulse1->carrier * 2 * fast_mult);  // (freq1 / out_rate) * (out_rate * 2));
              pulse1->off3 += pulse1->inc3;  // don't worry about fractional portion, frequency high enough to ignore
              pulse1->off3 = pulse1->off3 % sin_siz;  // mod with sin table size, to wrap offset
            }
            /*  Adjust split or split beat even when not playing beat */
            pulse1->split_now += pulse1->split_adj * fast_mult;
            if (pulse1->split_beat == 0.0 && pulse1->split_beat_adj == 0.0)
            {  // no split beat adjust, adjust split towards split_end
              if (pulse1->split_now < 0.0)
                pulse1->split_now = 0.0;
              else if (pulse1->split_now > 1.0)
                pulse1->split_now = 1.0;
            }
            else // split beat so oscillates between begin and end, and begin and end are fixed
            {
              if (pulse1->split_dist != 0.0)  // protect against division by zero below
              {
                  /* assumes split_end > split_begin, this is done in finish_beat_voice_setup */
                if (pulse1->split_now >= pulse1->split_end)  // larger than end
                {
                  double delta = fabs (pulse1->split_now - pulse1->split_end);  // overshoot
                  if (delta > pulse1->split_dist) // overshoot greater than split_dist
                  {
                    double quotient = delta/pulse1->split_dist;  // find number of wraps, including fraction
                    int counter = (int) floor (quotient);  // integer number of wraps
                    delta -= (double) counter;  // remainder after wraps taken away
                    if (counter % 2 == 0)  // even number of wraps
                    { 
                      pulse1->split_adj *= -1.;  // swap direction, reversing back towards split_begin
                      pulse1->split_now = pulse1->split_end - delta;  // rebound amount
                    }
                    else  // direction stays the same
                      pulse1->split_now = pulse1->split_begin + delta;  // rebound amount
                  }
                  else // overshoot smaller than overall split, reflect from end
                  {
                    pulse1->split_adj *= -1.;  // swap direction, reversing back towards split_begin
                    pulse1->split_now = pulse1->split_end - delta;  // rebound amount
                  }
                }
                else if (pulse1->split_now <= pulse1->split_begin)  // smaller than begin
                {
                  double delta = fabs (pulse1->split_begin - pulse1->split_now);  // overshoot
                  if (delta > pulse1->split_dist) // overshoot greater than split_dist
                  {
                    double quotient = delta/pulse1->split_dist;  // find number of wraps, including fraction
                    int counter = (int) floor (quotient);  // integer number of wraps
                    delta -= (double) counter;  // remainder after wraps taken away
                    if (counter % 2 == 0)  // even number of wraps
                    { 
                      pulse1->split_adj *= -1.;  // swap direction, reversing back towards split_end
                      pulse1->split_now = pulse1->split_begin + delta;  // rebound amount
                    }
                    else  // direction stays the same
                      pulse1->split_now = pulse1->split_end - delta;  // rebound amount
                  }
                  else // overshoot smaller than overall split, reflect from end
                  {
                    pulse1->split_adj *= -1.;  // swap direction, reversing back towards split_end
                    pulse1->split_now = pulse1->split_begin + delta;  // rebound amount
                  }
                }
              }
              /* Adjust the split beat and split adjust. */
              pulse1->split_beat += (pulse1->split_beat_adj * fast_mult);
              double sign_hold;  // variable to hold the current sign of the split adjustment for split beat oscillation
              if (pulse1->split_adj < 0.0)
                sign_hold = -1.0;
              else
                sign_hold = 1.0;
              pulse1->split_adj = ((pulse1->split_beat * 2. * pulse1->split_dist) / (double) out_rate);  
              pulse1->split_adj *= sign_hold;
            }  
            pulse1->carrier += (pulse1->carr_adj * fast_mult);  // tone to sound if time
            pulse1->beat += (pulse1->beat_adj * fast_mult);  // beat of the pulse
            pulse1->phase += (pulse1->phase_adj * fast_mult);  // beat of the pulse
            pulse1->time += (pulse1->time_adj * fast_mult);  // duration of the pulse
            pulse1->frames_left -= fast_mult;  // played pulse frame(s)
            pulse1->frames_right -= fast_mult;  // played pulse frame(s)
            pulse1->amp += (pulse1->amp_adj * fast_mult);  // amplitude to sound at
            if (pulse1->amp < 0.0)  // no negative amplitudes
              pulse1->amp = 0.0;
          }
        }
        break;
      case 14:                // Pulse tones step slide
      case 15:                // Pulse tones vary slide
        {
          double amp1;
          int off2_prev;
          pulse *pulse1;

          pulse1 = (pulse *) this;  // reassign void pointer as pulse struct

          for (ii= channels * offset; ii < channels * frame_count; ii+= channels)
          {
            if (pulse1->cur_frames >= pulse1->tot_frames)  // step voice finished
            {
              pulse *pulse2;
              pulse2 = pulse1->step_next;
              pulse2->next = pulse1->next;
              pulse2->prev = pulse1->prev;
              if (pulse1->prev != NULL)
                ((pulse *) pulse1->prev)->next = pulse2;
              else  // must be first voice in chain for time sequence
                snd1->voices = (void *) pulse2;
              if (pulse1->next != NULL)
                ((pulse *) pulse1->next)->prev = pulse2;
              /* free(pulse1); */  // not bothering to free, because it could slow down sound generation
              pulse1 = pulse2;  // new voice from step list
            }
            if (pulse1->first_pass)
            {
              pulse1->first_pass = 0;  // now active
              pulse1->fade_factor_left = 1.0; // set fade for left channel to start play
              pulse1->fade_factor_right = 1.0; // set fade for right channel to start play
              if (pulse1->last_off1 != NULL)  // there *is* a previous offset to use
                pulse1->off1 = *pulse1->last_off1;  // to eliminate crackle from discontinuity in wave
              if (pulse1->last_off3 != NULL)  // there *is* a previous offset to use
                pulse1->off3 = *pulse1->last_off3;  // to eliminate crackle from discontinuity in wave
              if (pulse1->last_off2 != NULL)  // there *is* a previous offset to use
                pulse1->off2 = *pulse1->last_off2;
            }
            off2_prev = pulse1->off2;  // save the original offset to determine if time to play pulse
            pulse1->inc2 += (fabs(pulse1->beat) * 2. * fast_mult);  //inc to next sin value, allow for -ve beat
            pulse1->off2 += (int) round(pulse1->inc2);  // offset for beat frequency into sin table
            pulse1->inc2 -= round (pulse1->inc2);  // remaining increment is only fractional part, +ve or -ve
            pulse1->off2 = pulse1->off2 % (out_rate * 2);  // mod with sin table size, to wrap offset
            int shift = (int) ((pulse1->phase/360.) * sin_siz);  // offset shift for phase
            if (pulse1->beat < 0.0)  // left channel leads
            {
              if (off2_prev > pulse1->off2)  // time to play left channel, beat offset just wrapped to start of sin table
                pulse1->frames_left = (int) (pulse1->time * out_rate);  // number of frames to play
              /* time to play right channel, shifted beat offset just wrapped to start of sin table */
              if ((off2_prev + shift) % sin_siz > (pulse1->off2 + shift) % sin_siz)
                pulse1->frames_right = (int) (pulse1->time * out_rate);  // number of frames to play
              /* fade out begins one millisecond from end  */
              if (pulse1->frames_left > 0 && pulse1->frames_left <= msec_fade_count)  
                pulse1->fade_factor_left -= (msec_fade_adjust * fast_mult); // adjust fade factor down
              if (pulse1->frames_right > 0 && pulse1->frames_right <= msec_fade_count)  
                pulse1->fade_factor_right -= (msec_fade_adjust * fast_mult); // adjust fade factor down
              if (pulse1->frames_left <= 0 && pulse1->frames_left > -fast_mult)  // have to allow for fast play
              { /* left pulse beat has ended for this pass, make sure ready for start of next beat play on left */
                pulse1->off1 = 0;  // always start at zero to eliminate beginning discontinuity
                pulse1->fade_factor_left = 1.0; // set start fade factor to full volume
              }
              if (pulse1->frames_right <= 0 && pulse1->frames_right > -fast_mult)  // have to allow for fast play
              { /* right pulse beat has ended for this pass, make sure ready for start of next beat play on right */
                pulse1->off3 = 0;  // always start at zero to eliminate beginning discontinuity
                pulse1->fade_factor_right = 1.0; // set start fade factor to full volume
              }
            }
            else if (pulse1->beat > 0.0)  // right channel leads
            {
              /* time to play left channel, shifted beat offset just wrapped to start of sin table */
              if ((off2_prev + shift) % sin_siz > (pulse1->off2 + shift) % sin_siz)
                pulse1->frames_left = (int) (pulse1->time * out_rate);  // number of frames to play
              if (off2_prev > pulse1->off2)  // time to play right channel, beat offset just wrapped to start of sin table
                pulse1->frames_right = (int) (pulse1->time * out_rate);  // number of frames to play
              /* fade out begins one millisecond from end  */
              if (pulse1->frames_left > 0 && pulse1->frames_left <= msec_fade_count)  
                pulse1->fade_factor_left -= (msec_fade_adjust * fast_mult); // adjust fade factor down
              if (pulse1->frames_right > 0 && pulse1->frames_right <= msec_fade_count)  
                pulse1->fade_factor_right -= (msec_fade_adjust * fast_mult); // adjust fade factor down
              if (pulse1->frames_left <= 0 && pulse1->frames_left > -fast_mult)  // have to allow for fast play
              { /* left pulse beat has ended for this pass, make sure ready for start of next beat play on left */
                pulse1->off1 = 0;  // always start at zero to eliminate beginning discontinuity
                pulse1->fade_factor_left = 1.0; // set start fade factor to full volume
              }
              if (pulse1->frames_right <= 0 && pulse1->frames_right > -fast_mult)  // have to allow for fast play
              { /* right pulse beat has ended for this pass, make sure ready for start of next beat play on right */
                pulse1->off3 = 0;  // always start at zero to eliminate beginning discontinuity
                pulse1->fade_factor_right = 1.0; // set start fade factor to full volume
              }
            }
            else  // in phase
            {
              if (off2_prev > pulse1->off2)  // time to play, beat offset just wrapped to start of sin table
              {
                pulse1->frames_left = (int) (pulse1->time * out_rate);  // number of frames to play
                pulse1->frames_right = (int) (pulse1->time * out_rate);  // number of frames to play
              }
              /* fade out begins one millisecond from end  */
              if (pulse1->frames_left > 0 && pulse1->frames_left <= msec_fade_count) 
              {
                pulse1->fade_factor_left -= (msec_fade_adjust * fast_mult); // adjust fade factor down
                pulse1->fade_factor_right -= (msec_fade_adjust * fast_mult); // adjust fade factor down
              }
              if (pulse1->frames_left <= 0 && pulse1->frames_left > -fast_mult)  // have to allow for fast play
              { /* pulse beat has ended for this pass, make sure ready for start of next beat play */
                pulse1->off1 = 0;  // always start at zero to eliminate beginning discontinuity
                pulse1->fade_factor_left = 1.0; // set start fade factor to full volume
                pulse1->off3 = 0;  // always start at zero to eliminate beginning discontinuity
                pulse1->fade_factor_right = 1.0; // set start fade factor to full volume
              }
            }
            if (pulse1->frames_left > 0)  // playing a pulse in left channel
            {
              if (opt_c)  // compensate
                amp1 = (pulse1->amp * amp_comp (pulse1->carrier));
              else
                amp1 = pulse1->amp;
              amp1 *= 2.;  // like binaural, double so each channel at amp with split
              /* pulse is always square wave, full volume  */
              out_buffer[ii] += (pulse1->split_now * amp1 * pulse1->fade_factor_left
                                                        * sin_table[pulse1->off1]);
              /* always start at zero, adjust at the end of pass so the zero not incremented on first pass */
              pulse1->inc1 = (int) round(pulse1->carrier * 2 * fast_mult);  // (freq1 / out_rate) * (out_rate * 2));
              pulse1->off1 += pulse1->inc1;  // don't worry about fractional portion, frequency high enough to ignore
              pulse1->off1 = pulse1->off1 % sin_siz;  // mod with sin table size, to wrap offset
            }
            if (pulse1->frames_right > 0)  // playing a pulse in right channel
            {
              if (opt_c)  // compensate
                amp1 = (pulse1->amp * amp_comp (pulse1->carrier));
              else
                amp1 = pulse1->amp;
              amp1 *= 2.;  // like binaural, double so each channel at amp with split
              /* pulse is always square wave, full volume  */
              out_buffer[ii+1] += ((1.0 - pulse1->split_now) * amp1 * pulse1->fade_factor_right
                                                        * sin_table[pulse1->off3]);
              /* always start at zero, adjust at the end of pass so the zero not incremented on first pass */
              pulse1->inc3 = (int) round(pulse1->carrier * 2 * fast_mult);  // (freq1 / out_rate) * (out_rate * 2));
              pulse1->off3 += pulse1->inc3;  // don't worry about fractional portion, frequency high enough to ignore
              pulse1->off3 = pulse1->off3 % sin_siz;  // mod with sin table size, to wrap offset
            }
            /*  Adjust split or split beat even when not playing beat */
            pulse1->split_now += pulse1->split_adj * fast_mult;
            if (pulse1->split_beat == 0.0)  // no split beat, adjust split towards split_end
            {
              if (pulse1->split_now < 0.0)
                pulse1->split_now = 0.0;
              else if (pulse1->split_now > 1.0)
                pulse1->split_now = 1.0;
            }
            else // split beat so oscillates between begin and end
            {
              if (pulse1->split_dist != 0.0)  // protect against division by zero below
              {
                  /* assumes split_end > split_begin, this is done in finish_beat_voice_setup */
                if (pulse1->split_now >= pulse1->split_end)  // larger than end
                {
                  double delta = fabs (pulse1->split_now - pulse1->split_end);  // overshoot
                  if (delta > pulse1->split_dist) // overshoot greater than split_dist
                  {
                    double quotient = delta/pulse1->split_dist;  // find number of wraps, including fraction
                    int counter = (int) floor (quotient);  // integer number of wraps
                    delta -= (double) counter;  // remainder after wraps taken away
                    if (counter % 2 == 0)  // even number of wraps
                    { 
                      pulse1->split_adj *= -1.;  // swap direction, reversing back towards split_begin
                      pulse1->split_now = pulse1->split_end - delta;  // rebound amount
                    }
                    else  // direction stays the same
                      pulse1->split_now = pulse1->split_begin + delta;  // rebound amount
                  }
                  else // overshoot smaller than overall split, reflect from end
                  {
                    pulse1->split_adj *= -1.;  // swap direction, reversing back towards split_begin
                    pulse1->split_now = pulse1->split_end - delta;  // rebound amount
                  }
                }
                else if (pulse1->split_now <= pulse1->split_begin)  // smaller than begin
                {
                  double delta = fabs (pulse1->split_begin - pulse1->split_now);  // overshoot
                  if (delta > pulse1->split_dist) // overshoot greater than split_dist
                  {
                    double quotient = delta/pulse1->split_dist;  // find number of wraps, including fraction
                    int counter = (int) floor (quotient);  // integer number of wraps
                    delta -= (double) counter;  // remainder after wraps taken away
                    if (counter % 2 == 0)  // even number of wraps
                    { 
                      pulse1->split_adj *= -1.;  // swap direction, reversing back towards split_end
                      pulse1->split_now = pulse1->split_begin + delta;  // rebound amount
                    }
                    else  // direction stays the same
                      pulse1->split_now = pulse1->split_end - delta;  // rebound amount
                  }
                  else // overshoot smaller than overall split, reflect from end
                  {
                    pulse1->split_adj *= -1.;  // swap direction, reversing back towards split_end
                    pulse1->split_now = pulse1->split_begin + delta;  // rebound amount
                  }
                }
              }
              /* Adjust the split beat and split adjust. */
              pulse1->split_beat += (pulse1->split_beat_adj * fast_mult);
              double sign_hold;  // variable to hold the current sign of the split adjustment for split beat oscillation
              if (pulse1->split_adj < 0.0)
                sign_hold = -1.0;
              else
                sign_hold = 1.0;
              pulse1->split_adj = ((pulse1->split_beat * 2. * pulse1->split_dist) / (double) out_rate);  
              pulse1->split_adj *= sign_hold;
            }  
            pulse1->carrier += (pulse1->carr_adj * fast_mult);  // tone to sound if time
            pulse1->beat += (pulse1->beat_adj * fast_mult);  // beat of the pulse
            pulse1->phase += (pulse1->phase_adj * fast_mult);  // beat of the pulse
            pulse1->time += (pulse1->time_adj * fast_mult);  // duration of the pulse
            pulse1->frames_left -= fast_mult;  // played pulse frame(s)
            pulse1->frames_right -= fast_mult;  // played pulse frame(s)
            pulse1->amp += (pulse1->amp_adj * fast_mult);  // amplitude to sound at
            if (pulse1->amp < 0.0)  // no negative amplitudes
              pulse1->amp = 0.0;
            pulse1->cur_frames += fast_mult;  
          }
        }
        break;
      case 16:                // phase tones
        {
          double amp1, amp2;
          phase *phase1;

          phase1 = (phase *) this;  // reassign void pointer as phase struct

          /* if start of the voice, set starting offset to be last offset of previous voice */
          if (phase1->first_pass)
          {
            phase1->first_pass = 0;  // now active
            if (phase1->last_off1 != NULL)  // there *is* a previous offset to use
              phase1->off1 = *phase1->last_off1;  // to eliminate crackle from discontinuity in wave
            if (phase1->last_amp_off1 != NULL)  // there *is* a previous amp_offset to use
              phase1->amp_off1 = *phase1->last_amp_off1;  // to eliminate crackle from discontinuity in wave
            if (phase1->last_amp_off2 != NULL)  // there *is* a previous amp_offset to use
              phase1->amp_off2 = *phase1->last_amp_off2;
            if (phase1->last_shift != NULL)  // there *is* a previous shift to use
              phase1->shift = *phase1->last_shift;  // to eliminate crackle from discontinuity in phase shift wave
            if (phase1->last_direction != NULL)  // there *is* a previous direction to use
              phase1->direction = *phase1->last_direction;  // to eliminate crackle from discontinuity in phase shift direction
          }
          for (ii= channels * offset; ii < channels * frame_count; ii+= channels)
          {
            if (opt_c)  // compensate
              amp1 = amp2 = (phase1->amp * amp_comp (phase1->carrier));
            else
              amp1 = amp2 = phase1->amp;
            /* perform the amplitude variation adjustment if required */
            if (phase1->amp_beat1 > 0.0)
            {
              phase1->amp_inc1 = (int) round(phase1->amp_beat1*2.);
              phase1->amp_off1 += phase1->amp_inc1;
              phase1->amp_off1 = phase1->amp_off1 % sin_siz;
              amp1 += ((amp1 * phase1->amp_pct1) * sin_table[phase1->amp_off1]);
            }
            if (phase1->amp_beat2 > 0.0)
            {
              phase1->amp_inc2 = (int) round(phase1->amp_beat2*2.);
              phase1->amp_off2 += phase1->amp_inc2;
              phase1->amp_off2 = phase1->amp_off2 % sin_siz;
              amp2 += ((amp2 * phase1->amp_pct2) * sin_table[phase1->amp_off2]);
            }
            phase1->inc1 = (int) round(phase1->carrier*2);  // (phase1->carrier / out_rate) * (out_rate * 2));
            phase1->off1 += phase1->inc1;
            phase1->off1 = phase1->off1 % sin_siz;  // base offset
            int max_shift = (int) ((phase1->phase/360.) * sin_siz);  // maximum offset shift allowed for phase
              /* shift offset adjust for this frame to satisfy the phase shift beat in sin table offset units */
            int shift_adjust = (int) (((phase1->phase/360.) * sin_siz * 2. * fabs(phase1->beat)) / out_rate);
              /* add this frame's shift adjust to the cumulative shift */
            phase1->shift += (shift_adjust * phase1->direction);  
            if (phase1->shift > max_shift)  // shifted too far away from base
            {
              if (max_shift != 0)   // there is shifting
              {
                if (((phase1->shift - max_shift) / max_shift) % 2 == 0)  // even number or zero of max_shift in overshoot
                  phase1->direction = -1;  // reversing back towards 0 phase shift
                phase1->shift = max_shift - ((phase1->shift - max_shift) % max_shift);  // rebound amount
              }
            }
            else if (phase1->shift < 0)  // shifted into lag to base
            {
              if (max_shift != 0)   // there is shifting
              {
                if ((abs(phase1->shift) / max_shift) % 2 == 0)  // even number or zero of max_shift in overshoot
                  phase1->direction = 1;  // reversing back towards maximum phase shift
                phase1->shift = (abs(phase1->shift)) % max_shift;  // rebound amount
              }
            }
            // else // inner case, already set above
            int phase_shifted_offset = (phase1->off1 + phase1->shift) % sin_siz;
            if (phase1->beat > 0.0)  // add the phase shift to the right channel
            {
              out_buffer[ii] += (amp1 * sin_table[phase1->off1]);
              out_buffer[ii+1] += (amp2 * sin_table[phase_shifted_offset]);  // right leads left
            }
            else if (phase1->beat < 0.0)  // add the phase shift to the left channel
            {
              out_buffer[ii] += (amp1 * sin_table[phase_shifted_offset]);  // left leads right
              out_buffer[ii+1] += (amp2 * sin_table[phase1->off1]);
            }
            else
            {
              if (phase1->beat_adj < 0.0)  // beat became zero from positive beat
              {
                out_buffer[ii] += (amp1 * sin_table[phase1->off1]);
                out_buffer[ii+1] += (amp2 * sin_table[phase_shifted_offset]);  // right leads left
              }
              else if (phase1->beat_adj > 0.0)  // beat became zero from negative beat
              {
                out_buffer[ii] += (amp1 * sin_table[phase_shifted_offset]);  // left leads right
                out_buffer[ii+1] += (amp2 * sin_table[phase1->off1]);
              }
              else // beat is constant zero
              {
                out_buffer[ii] += (amp1 * sin_table[phase1->off1]);  // in phase
                out_buffer[ii+1] += (amp2 * sin_table[phase1->off1]);
              }
            }
            if (phase1->slide)
            { /* adjust values for next pass only if this phase is sliding */
              phase1->carrier += (phase1->carr_adj * fast_mult);
              phase1->beat += (phase1->beat_adj * fast_mult);
              phase1->amp += (phase1->amp_adj * fast_mult);
              phase1->phase += (phase1->phase_adj * fast_mult);
              phase1->amp_beat1 += (phase1->amp_beat1_adj * fast_mult);
              phase1->amp_beat2 += (phase1->amp_beat2_adj * fast_mult);
              phase1->amp_pct1 += (phase1->amp_pct1_adj * fast_mult);
              phase1->amp_pct2 += (phase1->amp_pct2_adj * fast_mult);
            }
          }
        }
        break;
      case 17:                // phase tone, step slide, little less efficient, two extra checks each pass
      case 18:                // phase tone, vary slide, little less efficient, two extra checks each pass
        {
          double amp1, amp2;
          phase *phase1;

          phase1 = (phase *) this;  // reassign void pointer as phase struct
          for (ii= channels * offset; ii < channels * frame_count; ii+= channels)
          {
            if (phase1->cur_frames >= phase1->tot_frames)  // step voice finished
            {
              phase *phase2;
              phase2 = phase1->step_next;
              phase2->next = phase1->next;
              phase2->prev = phase1->prev;
              if (phase1->prev != NULL)
                ((phase *) phase1->prev)->next = phase2;
              else  // must be first voice in chain for time sequence
                snd1->voices = (void *) phase2;
              if (phase1->next != NULL)
                ((phase *) phase1->next)->prev = phase2;
              /* free(phase1); */  // not bothering to free, because it could slow down sound generation
              phase1 = phase2;  // new voice from step list
            }

            /* if start of the voice, set starting offset to be last offset of previous voice */
            if (phase1->first_pass)
            {
              phase1->first_pass = 0;  // now active
              if (phase1->last_off1 != NULL)  // there *is* a previous offset to use
                phase1->off1 = *phase1->last_off1;  // to eliminate crackle from discontinuity in wave
              if (phase1->last_amp_off1 != NULL)  // there *is* a previous amp_offset to use
                phase1->amp_off1 = *phase1->last_amp_off1;  // to eliminate crackle from discontinuity in wave
              if (phase1->last_amp_off2 != NULL)  // there *is* a previous amp_offset to use
                phase1->amp_off2 = *phase1->last_amp_off2;
              if (phase1->last_shift != NULL)  // there *is* a previous shift to use
                phase1->shift = *phase1->last_shift;  // to eliminate crackle from discontinuity in phase shift wave
              if (phase1->last_direction != NULL)  // there *is* a previous direction to use
                phase1->direction = *phase1->last_direction; // to eliminate crackle from discontinuity in phase shift direction
            }
            if (opt_c)  // compensate
              amp1 = amp2 = (phase1->amp * amp_comp (phase1->carrier));
            else
              amp1 = amp2 = phase1->amp;
            /* perform the amplitude variation adjustment if required */
            if (phase1->amp_beat1 > 0.0)
            {
              phase1->amp_inc1 = (int) round(phase1->amp_beat1*2);
              phase1->amp_off1 += phase1->amp_inc1;
              phase1->amp_off1 = phase1->amp_off1 % (out_rate * 2);
              amp1 += ((amp1 * phase1->amp_pct1) * sin_table[phase1->amp_off1]);
            }
            if (phase1->amp_beat2 > 0.0)
            {
              phase1->amp_inc2 = (int) round(phase1->amp_beat2*2);
              phase1->amp_off2 += phase1->amp_inc2;
              phase1->amp_off2 = phase1->amp_off2 % (out_rate * 2);
              amp2 += ((amp2 * phase1->amp_pct2) * sin_table[phase1->amp_off2]);
            }
            phase1->inc1 = (int) round(phase1->carrier*2);  // (phase1->carrier / out_rate) * (out_rate * 2));
            phase1->off1 += phase1->inc1;
            phase1->off1 = phase1->off1 % sin_siz;  // base offset
            int max_shift = (int) ((phase1->phase/360.) * sin_siz);  // maximum offset shift allowed for phase
              /* shift offset adjust for this frame to satisfy the phase shift beat in sin table offset units */
            int shift_adjust = (int) (((phase1->phase/360.) * sin_siz * 2. * phase1->beat) / out_rate);
              /* add this frame's shift adjust to the cumulative shift */
            phase1->shift += (shift_adjust * phase1->direction);  
            if (phase1->shift > max_shift)  // shifted too far away from base
            {
              if (max_shift != 0)   // there is shifting
              {
                if (((phase1->shift - max_shift) / max_shift) % 2 == 0)  // even number or zero of max_shift in overshoot
                  phase1->direction = -1;  // reversing back towards 0 phase shift
                phase1->shift = max_shift - ((phase1->shift - max_shift) % max_shift);  // rebound amount
              }
            }
            else if (phase1->shift < 0)  // shifted into lag to base
            {
              if (max_shift != 0)   // there is shifting
              {
                if ((abs(phase1->shift) / max_shift) % 2 == 0)  // even number or zero of max_shift in overshoot
                  phase1->direction = 1;  // reversing back towards maximum phase shift
                phase1->shift = (abs(phase1->shift)) % max_shift;  // rebound amount
              }
            }
            // else // inner case, already set above
            int phase_shifted_offset = (phase1->off1 + phase1->shift) % sin_siz;
            if (phase1->beat > 0.0)  // add the phase shift to the right channel
            {
              out_buffer[ii] += (amp1 * sin_table[phase1->off1]);
              out_buffer[ii+1] += (amp2 * sin_table[phase_shifted_offset]);  // right leads left
            }
            else if (phase1->beat < 0.0)  // add the phase shift to the left channel
            {
              out_buffer[ii] += (amp1 * sin_table[phase_shifted_offset]);  // left leads right
              out_buffer[ii+1] += (amp2 * sin_table[phase1->off1]);
            }
            else
            {
              out_buffer[ii] += (amp1 * sin_table[phase1->off1]);  // in phase
              out_buffer[ii+1] += (amp2 * sin_table[phase1->off1]);
            }
            if (phase1->slide)
            { /* adjust values for next pass only if this phase is sliding */
              phase1->carrier += (phase1->carr_adj * fast_mult);
              phase1->beat += (phase1->beat_adj * fast_mult);
              phase1->amp += (phase1->amp_adj * fast_mult);
              phase1->phase += (phase1->phase_adj * fast_mult);
              phase1->amp_beat1 += (phase1->amp_beat1_adj * fast_mult);
              phase1->amp_beat2 += (phase1->amp_beat2_adj * fast_mult);
              phase1->amp_pct1 += (phase1->amp_pct1_adj * fast_mult);
              phase1->amp_pct2 += (phase1->amp_pct2_adj * fast_mult);
            }
            phase1->cur_frames += 1 * fast_mult;  
          }
        }
        break;
      case 19:                // fm tones
        {
          double amp1, amp2;
          fm *fm1;

          fm1 = (fm *) this;  // reassign void pointer as fm struct

          /* if start of the voice, set starting offset to be last offset of previous voice */
          if (fm1->first_pass)
          {
            fm1->first_pass = 0;  // now active
            if (fm1->last_off1 != NULL)  // there *is* a previous offset to use
              fm1->off1 = *fm1->last_off1;  // to eliminate crackle from discontinuity in wave
            if (fm1->last_amp_off1 != NULL)  // there *is* a previous amp_offset to use
              fm1->amp_off1 = *fm1->last_amp_off1;  // to eliminate crackle from discontinuity in wave
            if (fm1->last_amp_off2 != NULL)  // there *is* a previous amp_offset to use
              fm1->amp_off2 = *fm1->last_amp_off2;
            if (fm1->last_shift != NULL)  // there *is* a previous shift to use
              fm1->shift = *fm1->last_shift;  // to eliminate crackle from discontinuity in phase shift wave
            if (fm1->last_direction != NULL)  // there *is* a previous direction to use
              fm1->direction = *fm1->last_direction;  // to eliminate crackle from discontinuity in phase shift direction
          }
          for (ii= channels * offset; ii < channels * frame_count; ii+= channels)
          {
            if (opt_c)  // compensate
              amp1 = amp2 = (fm1->amp * amp_comp (fm1->carrier));
            else
              amp1 = amp2 = fm1->amp;
            /* perform the amplitude variation adjustment if required */
            if (fm1->amp_beat1 > 0.0)
            {
              fm1->amp_inc1 = (int) round(fm1->amp_beat1*2.);
              fm1->amp_off1 += fm1->amp_inc1;
              fm1->amp_off1 = fm1->amp_off1 % sin_siz;
              amp1 += ((amp1 * fm1->amp_pct1) * sin_table[fm1->amp_off1]);
            }
            if (fm1->amp_beat2 > 0.0)
            {
              fm1->amp_inc2 = (int) round(fm1->amp_beat2*2.);
              fm1->amp_off2 += fm1->amp_inc2;
              fm1->amp_off2 = fm1->amp_off2 % sin_siz;
              amp2 += ((amp2 * fm1->amp_pct2) * sin_table[fm1->amp_off2]);
            }
            fm1->inc1 = (int) round((fm1->carrier+fm1->shift)*2);  // (fm1->carrier / out_rate) * (out_rate * 2));
            fm1->off1 += fm1->inc1;
            fm1->off1 = fm1->off1 % sin_siz;  // base offset
            if (fm1->channel == 1)  // left channel only playing
              out_buffer[ii] += (amp1 * sin_table[fm1->off1]);
            else if (fm1->channel == 2)  // right channel only playing
              out_buffer[ii+1] += (amp2 * sin_table[fm1->off1]);
            else if (fm1->channel == 3)  // both channels are playing
            {
              int phase_offset = (int) ((fabs(fm1->phase)/360.) * sin_siz);  // offset shift for phase
              int phase_shifted_offset = (fm1->off1 + phase_offset) % sin_siz;
              if (fm1->phase > 0.0)  // add the phase shift to the right channel
              {
                out_buffer[ii] += (amp1 * sin_table[fm1->off1]);
                out_buffer[ii+1] += (amp2 * sin_table[phase_shifted_offset]);  // right leads left
              }
              else if (fm1->phase < 0.0)  // add the phase shift to the left channel
              {
                out_buffer[ii] += (amp1 * sin_table[phase_shifted_offset]);  // left leads right
                out_buffer[ii+1] += (amp2 * sin_table[fm1->off1]);
              }
            }
              /* Adjustment to make to the carrier frequency addition so the band occurs beat times per second */
            double shift_adjust = ((2. * fm1->band * fm1->beat) / out_rate);  // 2 because back and forth
            fm1->shift += (shift_adjust * fm1->direction);  
            if (fm1->shift > fm1->band)  // shifted too far away from base carrier
            {
              if (fm1->band != 0)   // there is frequency beat
              {
                if (((fm1->shift - fm1->band) <  fm1->band))  // overshoot is less than fm1->band
                {
                  fm1->direction = -1;  // reversing back towards 0
                  fm1->shift = fm1->band - (fm1->shift - fm1->band);  // rebound amount
                }
                else  // overshoot greater than band
                {
                  int counter = 0;
                  while (((fm1->shift - fm1->band) >  fm1->band))  // until overshoot is less than fm1->band
                  { 
                    fm1->shift -= fm1->band;
                    counter++;
                  }
                  if (counter % 2 == 0)  // even number of wraps
                  { 
                    fm1->direction = -1;  // reversing back towards 0
                    fm1->shift = fm1->band - fm1->shift;  // rebound amount
                  }
                  else  // directions stays the same
                    fm1->shift = fm1->shift;  // rebound amount
                }
              }
            }
            else if (fm1->shift < 0.0)  // shifted into negative to carrier
            {
              if (fm1->band != 0)   // there is frequency beat
              {
                if ((fabs(fm1->shift) <  fm1->band))  // overshoot is less than fm1->band
                {
                  fm1->direction = 1;  // reversing back towards band
                  fm1->shift = fabs(fm1->shift);  // rebound amount
                }
                else  // overshoot greater than band
                {
                  int counter = 0;
                  while ((fabs(fm1->shift) >  fm1->band))  // overshoot is greater than fm1->band
                  { 
                    fm1->shift += fm1->band;
                    counter++;
                  }
                  if (counter % 2 == 0)  // even number of wraps
                  { 
                    fm1->direction = 1;  // reversing back towards band
                    fm1->shift = fabs(fm1->shift);  // rebound amount
                  }
                  else  // directions stays the same
                    fm1->shift = fm1->band - fabs(fm1->shift);  // rebound amount
                }
              }
            }
            // else // inner case, already set above as initial condition
            if (fm1->slide)
            { /* adjust values for next pass only if this phase is sliding */
              fm1->carrier += (fm1->carr_adj * fast_mult);
              fm1->beat += (fm1->beat_adj * fast_mult);
              fm1->amp += (fm1->amp_adj * fast_mult);
              fm1->phase += (fm1->phase_adj * fast_mult);
              fm1->band += (fm1->band_adj * fast_mult);
              fm1->amp_beat1 += (fm1->amp_beat1_adj * fast_mult);
              fm1->amp_beat2 += (fm1->amp_beat2_adj * fast_mult);
              fm1->amp_pct1 += (fm1->amp_pct1_adj * fast_mult);
              fm1->amp_pct2 += (fm1->amp_pct2_adj * fast_mult);
            }
          }
        }
        break;
      case 20:                // fm tone, step slide, little less efficient, two extra checks each pass
      case 21:                // fm tone, vary slide, little less efficient, two extra checks each pass
        {
          double amp1, amp2;
          fm *fm1;

          fm1 = (fm *) this;  // reassign void pointer as fm struct
          for (ii= channels * offset; ii < channels * frame_count; ii+= channels)
          {
            if (fm1->cur_frames >= fm1->tot_frames)  // step voice finished
            {
              fm *fm2;
              fm2 = fm1->step_next;
              fm2->next = fm1->next;
              fm2->prev = fm1->prev;
              if (fm1->prev != NULL)
                ((fm *) fm1->prev)->next = fm2;
              else  // must be first voice in chain for time sequence
                snd1->voices = (void *) fm2;
              if (fm1->next != NULL)
                ((fm *) fm1->next)->prev = fm2;
              /* free(fm1); */  // not bothering to free, because it could slow down sound generation
              fm1 = fm2;  // new voice from step list
            }

            /* if start of the voice, set starting offset to be last offset of previous voice */
            if (fm1->first_pass)
            {
              fm1->first_pass = 0;  // now active
              if (fm1->last_off1 != NULL)  // there *is* a previous offset to use
                fm1->off1 = *fm1->last_off1;  // to eliminate crackle from discontinuity in wave
              if (fm1->last_amp_off1 != NULL)  // there *is* a previous amp_offset to use
                fm1->amp_off1 = *fm1->last_amp_off1;  // to eliminate crackle from discontinuity in wave
              if (fm1->last_amp_off2 != NULL)  // there *is* a previous amp_offset to use
                fm1->amp_off2 = *fm1->last_amp_off2;
              if (fm1->last_shift != NULL)  // there *is* a previous shift to use
                fm1->shift = *fm1->last_shift;  // to eliminate crackle from discontinuity in phase shift wave
              if (fm1->last_direction != NULL)  // there *is* a previous direction to use
                fm1->direction = *fm1->last_direction; // to eliminate crackle from discontinuity in phase shift direction
            }
            if (opt_c)  // compensate
              amp1 = amp2 = (fm1->amp * amp_comp (fm1->carrier));
            else
              amp1 = amp2 = fm1->amp;
            /* perform the amplitude variation adjustment if required */
            if (fm1->amp_beat1 > 0.0)
            {
              fm1->amp_inc1 = (int) round(fm1->amp_beat1*2);
              fm1->amp_off1 += fm1->amp_inc1;
              fm1->amp_off1 = fm1->amp_off1 % (out_rate * 2);
              amp1 += ((amp1 * fm1->amp_pct1) * sin_table[fm1->amp_off1]);
            }
            if (fm1->amp_beat2 > 0.0)
            {
              fm1->amp_inc2 = (int) round(fm1->amp_beat2*2);
              fm1->amp_off2 += fm1->amp_inc2;
              fm1->amp_off2 = fm1->amp_off2 % (out_rate * 2);
              amp2 += ((amp2 * fm1->amp_pct2) * sin_table[fm1->amp_off2]);
            }
            fm1->inc1 = (int) round((fm1->carrier+fm1->shift)*2);  // (fm1->carrier / out_rate) * (out_rate * 2));
            fm1->off1 += fm1->inc1;
            fm1->off1 = fm1->off1 % sin_siz;  // base offset
            if (fm1->channel == 1)  // left channel only playing
              out_buffer[ii] += (amp1 * sin_table[fm1->off1]);
            else if (fm1->channel == 2)  // right channel only playing
              out_buffer[ii+1] += (amp2 * sin_table[fm1->off1]);
            else if (fm1->channel == 3)  // both channels are playing
            {
              int phase_offset = (int) ((fabs(fm1->phase)/360.) * sin_siz);  // offset shift for phase
              int phase_shifted_offset = (fm1->off1 + phase_offset) % sin_siz;
              if (fm1->phase > 0.0)  // add the phase shift to the right channel
              {
                out_buffer[ii] += (amp1 * sin_table[fm1->off1]);
                out_buffer[ii+1] += (amp2 * sin_table[phase_shifted_offset]);  // right leads left
              }
              else if (fm1->phase < 0.0)  // add the phase shift to the left channel
              {
                out_buffer[ii] += (amp1 * sin_table[phase_shifted_offset]);  // left leads right
                out_buffer[ii+1] += (amp2 * sin_table[fm1->off1]);
              }
            }
              /* Adjustment to make to the carrier frequency addition so the band occurs beat times per second */
            double shift_adjust = ((2. * fm1->band * fm1->beat) / out_rate);  // 2 because back and forth
            fm1->shift += (shift_adjust * fm1->direction);  
            if (fm1->shift > fm1->band)  // shifted too far away from base carrier
            {
              if (fm1->band != 0)   // there is frequency beat
              {
                if (((fm1->shift - fm1->band) <  fm1->band))  // overshoot is less than fm1->band
                {
                  fm1->direction = -1;  // reversing back towards 0
                  fm1->shift = fm1->band - (fm1->shift - fm1->band);  // rebound amount
                }
                else  // overshoot greater than band
                {
                  int counter = 0;
                  while (((fm1->shift - fm1->band) >  fm1->band))  // overshoot is less than fm1->band
                  { 
                    fm1->shift -= fm1->band;
                    counter++;
                  }
                  if (counter % 2 == 0)  // even number of wraps
                  { 
                    fm1->direction = -1;  // reversing back towards 0, rebound amount set by while above
                    fm1->shift = fm1->band - fm1->shift;  // rebound amount
                  }
                  else  // directions stays the same
                    fm1->shift = fm1->shift;  // rebound amount
                }
              }
            }
            else if (fm1->shift < 0.0)  // shifted into negative to carrier
            {
              if (fm1->band != 0)   // there is frequency beat
              {
                if ((fabs(fm1->shift) <  fm1->band))  // overshoot is less than fm1->band
                {
                  fm1->direction = 1;  // reversing back towards band
                  fm1->shift = fabs(fm1->shift);  // rebound amount
                }
                else  // overshoot greater than band
                {
                  int counter = 0;
                  while ((fabs(fm1->shift) >  fm1->band))  // overshoot is greater than fm1->band
                  { 
                    fm1->shift += fm1->band;
                    counter++;
                  }
                  if (counter % 2 == 0)  // even number of wraps
                  { 
                    fm1->direction = 1;  // reversing back towards band
                    fm1->shift = fabs(fm1->shift);  // rebound amount
                  }
                  else  // directions stays the same
                    fm1->shift = fm1->band - fabs(fm1->shift);  // rebound amount
                }
              }
            }
            // else // inner case, already set above as initial condition
            if (fm1->slide)
            { /* adjust values for next pass only if this phase is sliding */
              fm1->carrier += (fm1->carr_adj * fast_mult);
              fm1->beat += (fm1->beat_adj * fast_mult);
              fm1->amp += (fm1->amp_adj * fast_mult);
              fm1->phase += (fm1->phase_adj * fast_mult);
              fm1->band += (fm1->band_adj * fast_mult);
              fm1->amp_beat1 += (fm1->amp_beat1_adj * fast_mult);
              fm1->amp_beat2 += (fm1->amp_beat2_adj * fast_mult);
              fm1->amp_pct1 += (fm1->amp_pct1_adj * fast_mult);
              fm1->amp_pct2 += (fm1->amp_pct2_adj * fast_mult);
            }
            fm1->cur_frames += 1 * fast_mult;  
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
  // allow main to call again, locked by caller
  pthread_mutex_unlock (&mtx_status);
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
        char_count += fprintf (fp, " %.3e %.3e %.3e\n", binaural1->carr_adj, binaural1->beat_adj, binaural1->amp_adj);
        char_count += fprintf (fp, "       %.3e %.3e", binaural1->amp_beat1_adj, binaural1->amp_beat2_adj);
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
        char_count += fprintf (fp, " %d\n", bell1->behave);
        char_count += fprintf (fp, "        %d %d %lld %lld %lld",
                        bell1->inc1, bell1->off1, bell1->next_play, bell1->sofar, bell1->ring);
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
        char_count += fprintf (fp, " %lld %lld %lld %lld\n",
                        noise1->length_min, noise1->length_max, noise1->repeat_min, noise1->repeat_max);
        char_count += fprintf (fp, "         %d %d %d %lld %lld %lld",
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
        char_count += fprintf (fp, " %lld %lld %lld",
                        sample1->size, sample1->off1, sample1->play);
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
        char_count += fprintf (fp, " %lld %lld",
                        repeat1->off1, repeat1->play);
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
        char_count += fprintf (fp, " %lld", once1->play_when);
        char_count += fprintf (fp, " %lld %lld %lld", once1->sofar, once1->off1, once1->play);
        char_count += fprintf (fp, " %.3e %d %d\n", once1->split_adj, once1->mono, once1->not_played);
      }
      break;
    case 8:  // chronaural
      {
        chronaural *chronaural1;

        chronaural1 = (chronaural *) this;
        char_count += fprintf (fp, "   chron %.3f", chronaural1->carrier);
        char_count += fprintf (fp, " %.3f", chronaural1->beat);
        char_count += fprintf (fp, " %.3f %.3f %.3e", AMP_DA(chronaural1->amp), chronaural1->phase, chronaural1->sin_threshold);
        char_count += fprintf (fp, " %d", chronaural1->beat_behave);
        char_count += fprintf (fp, " %d %d", chronaural1->inc1, chronaural1->off1);
        char_count += fprintf (fp, " %d %d", chronaural1->inc3, chronaural1->off3);
        char_count += fprintf (fp, " %.3f %d", chronaural1->inc2, chronaural1->off2);
        char_count += fprintf (fp, " %.3e %.3e %.3e", chronaural1->carr_adj, chronaural1->beat_adj, chronaural1->amp_adj);
        char_count += fprintf (fp, " %.3f", chronaural1->split_now );
        char_count += fprintf (fp, " %.3f %.3f\n         %.3f %.3f",
                        chronaural1->split_begin, chronaural1->split_end, chronaural1->split_low, chronaural1->split_high);
        char_count += fprintf (fp, " %.3f %.3f %.3f %.3f",
                      chronaural1->fade_sinval, chronaural1->fade_sinval2, chronaural1->fade_factor, chronaural1->fade_factor2);
        char_count += fprintf (fp, " %.3e", chronaural1->split_beat);
        char_count += fprintf (fp, " %.3e %.3e",
                        chronaural1->split_beat_adj, chronaural1->split_adj);
        char_count += fprintf (fp, " %d\n", chronaural1->slide);
      }
      break;
    case 9:  // binaural step slide
    case 11:  // binaural vary slide, even though doesn't have fuzz
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
        char_count += fprintf (fp, " %.3e %.3e %.3e\n", binaural1->carr_adj, binaural1->beat_adj, binaural1->amp_adj);
        char_count += fprintf (fp, "       %.3e %.3e", binaural1->amp_beat1_adj, binaural1->amp_beat2_adj);
        char_count += fprintf (fp, " %.3e %.3e", binaural1->amp_pct1_adj, binaural1->amp_pct2_adj);
        char_count += fprintf (fp, " %d", binaural1->slide);
        char_count += fprintf (fp, " %lld %lld", binaural1->tot_frames, binaural1->cur_frames);
        char_count += fprintf (fp, "\n       %d %.2f %.1f\n", binaural1->steps, binaural1->slide_time, binaural1->fuzz);
      }
      break;
    case 10:  // chronaural step slide
    case 12:  // chronaural vary slide, even though doesn't have fuzz
      {
        chronaural *chronaural1;

        chronaural1 = (chronaural *) this;
        char_count += fprintf (fp, "   chron %.3f", chronaural1->carrier);
        char_count += fprintf (fp, " %.3f", chronaural1->beat);
        char_count += fprintf (fp, " %.3f %.3f %.3e", AMP_DA(chronaural1->amp), chronaural1->phase, chronaural1->sin_threshold);
        char_count += fprintf (fp, " %d", chronaural1->beat_behave);
        char_count += fprintf (fp, " %d %d", chronaural1->inc1, chronaural1->off1);
        char_count += fprintf (fp, " %d %d", chronaural1->inc3, chronaural1->off3);
        char_count += fprintf (fp, " %.3f %d", chronaural1->inc2, chronaural1->off2);
        char_count += fprintf (fp, " %.3e %.3e %.3e", chronaural1->carr_adj, chronaural1->beat_adj, chronaural1->amp_adj);
        char_count += fprintf (fp, " %.3f", chronaural1->split_now );
        char_count += fprintf (fp, " %.3f %.3f\n         %.3f %.3f",
                        chronaural1->split_begin, chronaural1->split_end, chronaural1->split_low, chronaural1->split_high);
        char_count += fprintf (fp, " %.3f %.3f %.3f %.3f",
                      chronaural1->fade_sinval, chronaural1->fade_sinval2, chronaural1->fade_factor, chronaural1->fade_factor2);
        char_count += fprintf (fp, " %.3e", chronaural1->split_beat);
        char_count += fprintf (fp, " %.3e %.3e",
                        chronaural1->split_beat_adj, chronaural1->split_adj);
        char_count += fprintf (fp, " %d", chronaural1->slide);
        char_count += fprintf (fp, " %lld %lld", chronaural1->tot_frames, chronaural1->cur_frames);
        char_count += fprintf (fp, "\n         %d %.2f %.1f\n", chronaural1->steps, chronaural1->slide_time, chronaural1->fuzz);
      }
      break;
    case 13:  // pulse
      {
        pulse *pulse1;

        pulse1 = (pulse *) this;
        char_count += fprintf (fp, "   pulse %.3f", pulse1->carrier);
        char_count += fprintf (fp, " %.3f", pulse1->beat);
        char_count += fprintf (fp, " %.3f %.3f %.3f", AMP_DA (pulse1->amp), pulse1->phase, pulse1->time);
        char_count += fprintf (fp, " %d %d", pulse1->frames_left, pulse1->frames_right);
        char_count += fprintf (fp, " %d %d", pulse1->inc1, pulse1->off1);
        char_count += fprintf (fp, " %d %d", pulse1->inc3, pulse1->off3);
        char_count += fprintf (fp, " %.3f %d", pulse1->inc2, pulse1->off2);
        char_count += fprintf (fp, " %.3e %.3e %.3e\n         %.3e %.3e", pulse1->carr_adj, 
                                                            pulse1->beat_adj, pulse1->phase_adj, 
                                                            pulse1->time_adj, pulse1->amp_adj);
        char_count += fprintf (fp, " %.3f", pulse1->split_now );
        char_count += fprintf (fp, " %.3f %.3f %.3f %.3f", pulse1->split_begin, pulse1->split_end, 
                                                              pulse1->split_low, pulse1->split_high);
        char_count += fprintf (fp, " %.3f %.3f", pulse1->fade_factor_left, pulse1->fade_factor_right);
        char_count += fprintf (fp, " %.3e", pulse1->split_beat);
        char_count += fprintf (fp, " %.3e %.3e", pulse1->split_beat_adj, pulse1->split_adj);
        char_count += fprintf (fp, " %d\n", pulse1->slide);
      }
      break;
    case 14:  // pulse step slide
    case 15:  // pulse vary slide, even though doesn't have fuzz
      {
        pulse *pulse1;

        pulse1 = (pulse *) this;
        char_count += fprintf (fp, "   pulse %.3f", pulse1->carrier);
        char_count += fprintf (fp, " %.3f", pulse1->beat);
        char_count += fprintf (fp, " %.3f %.3f %.3f", AMP_DA (pulse1->amp), pulse1->phase, pulse1->time);
        char_count += fprintf (fp, " %d %d", pulse1->frames_left, pulse1->frames_right);
        char_count += fprintf (fp, " %d %d", pulse1->inc1, pulse1->off1);
        char_count += fprintf (fp, " %d %d", pulse1->inc3, pulse1->off3);
        char_count += fprintf (fp, " %.3f %d", pulse1->inc2, pulse1->off2);
        char_count += fprintf (fp, " %.3e %.3e %.3e\n         %.3e %.3e", pulse1->carr_adj, 
                                                            pulse1->beat_adj, pulse1->phase_adj, 
                                                            pulse1->time_adj, pulse1->amp_adj);
        char_count += fprintf (fp, " %.3f", pulse1->split_now );
        char_count += fprintf (fp, " %.3f %.3f %.3f %.3f", pulse1->split_begin, pulse1->split_end, 
                                                              pulse1->split_low, pulse1->split_high);
        char_count += fprintf (fp, " %.3f %.3f", pulse1->fade_factor_left, pulse1->fade_factor_right);
        char_count += fprintf (fp, " %.3e", pulse1->split_beat);
        char_count += fprintf (fp, " %.3e %.3e", pulse1->split_beat_adj, pulse1->split_adj);
        char_count += fprintf (fp, " %d", pulse1->slide);
        char_count += fprintf (fp, " %lld %lld", pulse1->tot_frames, pulse1->cur_frames);
        char_count += fprintf (fp, "\n         %d %.2f %.1f\n", pulse1->steps, pulse1->slide_time, pulse1->fuzz);
      }
      break;
    case 16:  // phase
      {
        phase *phase1;

        phase1 = (phase *) this;
        char_count += fprintf (fp, "   phase %.3f %+.3f", phase1->carrier, phase1->beat);
        char_count += fprintf (fp, " %.3f %.3f", AMP_DA (phase1->amp), phase1->phase);
        char_count += fprintf (fp, " %.3f %.3f", phase1->amp_beat1, phase1->amp_beat2);
        char_count += fprintf (fp, " %.3f %.3f", AMP_DA (phase1->amp_pct1), AMP_DA (phase1->amp_pct2));
        char_count += fprintf (fp, " %d %d %d %d", phase1->inc1, phase1->off1, phase1->shift, phase1->direction);
        char_count += fprintf (fp, " %d %d %d %d\n", 
                                   phase1->amp_inc1, phase1->amp_off1, phase1->amp_inc2, phase1->amp_off2);
        char_count += fprintf (fp, "       %.3e %.3e %.3e %.3e", 
                                   phase1->carr_adj, phase1->beat_adj, phase1->amp_adj, phase1->phase_adj);
        char_count += fprintf (fp, " %.3e %.3e", phase1->amp_beat1_adj, phase1->amp_beat2_adj);
        char_count += fprintf (fp, " %.3e %.3e", phase1->amp_pct1_adj, phase1->amp_pct2_adj);
        char_count += fprintf (fp, " %d\n", phase1->slide);
      }
      break;
    case 17:  // phase step slide
    case 18:  // phase vary slide, even though doesn't have fuzz
      {
        phase *phase1;

        phase1 = (phase *) this;
        char_count += fprintf (fp, "   phase %.3f %+.3f", phase1->carrier, phase1->beat);
        char_count += fprintf (fp, " %.3f %.3f", AMP_DA (phase1->amp), phase1->phase);
        char_count += fprintf (fp, " %.3f %.3f", phase1->amp_beat1, phase1->amp_beat2);
        char_count += fprintf (fp, " %.3f %.3f", AMP_DA (phase1->amp_pct1), AMP_DA (phase1->amp_pct2));
        char_count += fprintf (fp, " %d %d %d %d", phase1->inc1, phase1->off1, phase1->shift, phase1->direction);
        char_count += fprintf (fp, " %d %d %d %d", 
                                   phase1->amp_inc1, phase1->amp_off1, phase1->amp_inc2, phase1->amp_off2);
        char_count += fprintf (fp, "\n       %.3e %.3e %.3e %.3e", 
                                   phase1->carr_adj, phase1->beat_adj, phase1->amp_adj, phase1->phase_adj);
        char_count += fprintf (fp, " %.3e %.3e", phase1->amp_beat1_adj, phase1->amp_beat2_adj);
        char_count += fprintf (fp, " %.3e %.3e", phase1->amp_pct1_adj, phase1->amp_pct2_adj);
        char_count += fprintf (fp, " %d", phase1->slide);
        char_count += fprintf (fp, " %lld %lld", phase1->tot_frames, phase1->cur_frames);
        char_count += fprintf (fp, "\n       %d %.2f %.1f\n", phase1->steps, phase1->slide_time, phase1->fuzz);
      }
      break;
    case 19:  // fm
      {
        fm *fm1;

        fm1 = (fm *) this;
        char_count += fprintf (fp, "   fm %.3f %+.3f", fm1->carrier, fm1->beat);
        char_count += fprintf (fp, " %.3f %.3f %c %.3f", 
                                    AMP_DA (fm1->amp), fm1->band, fm1->channel, fm1->phase);
        char_count += fprintf (fp, " %.3f %.3f", fm1->amp_beat1, fm1->amp_beat2);
        char_count += fprintf (fp, " %.3f %.3f", AMP_DA (fm1->amp_pct1), AMP_DA (fm1->amp_pct2));
        char_count += fprintf (fp, " %d %d %.3f %d", fm1->inc1, fm1->off1, fm1->shift, fm1->direction);
        char_count += fprintf (fp, " %d %d %d %d\n", 
                                   fm1->amp_inc1, fm1->amp_off1, fm1->amp_inc2, fm1->amp_off2);
        char_count += fprintf (fp, "       %.3e %.3e %.3e %.3e", 
                                   fm1->carr_adj, fm1->beat_adj, fm1->amp_adj, fm1->phase_adj);
        char_count += fprintf (fp, " %.3e", fm1->band_adj);
        char_count += fprintf (fp, " %.3e %.3e", fm1->amp_beat1_adj, fm1->amp_beat2_adj);
        char_count += fprintf (fp, " %.3e %.3e", fm1->amp_pct1_adj, fm1->amp_pct2_adj);
        char_count += fprintf (fp, " %d\n", fm1->slide);
      }
      break;
    case 20:  // fm step slide
    case 21:  // fm vary slide, even though doesn't have fuzz
      {
        fm *fm1;

        fm1 = (fm *) this;
        char_count += fprintf (fp, "   fm %.3f %+.3f", fm1->carrier, fm1->beat);
        char_count += fprintf (fp, " %.3f %.3f %c %.3f", 
                                    AMP_DA (fm1->amp), fm1->band, fm1->channel, fm1->phase);
        char_count += fprintf (fp, " %.3f %.3f", fm1->amp_beat1, fm1->amp_beat2);
        char_count += fprintf (fp, " %.3f %.3f", AMP_DA (fm1->amp_pct1), AMP_DA (fm1->amp_pct2));
        char_count += fprintf (fp, " %d %d %.3f %d", fm1->inc1, fm1->off1, fm1->shift, fm1->direction);
        char_count += fprintf (fp, " %d %d %d %d", 
                                   fm1->amp_inc1, fm1->amp_off1, fm1->amp_inc2, fm1->amp_off2);
        char_count += fprintf (fp, "\n       %.3e %.3e %.3e %.3e", 
                                   fm1->carr_adj, fm1->beat_adj, fm1->amp_adj, fm1->phase_adj);
        char_count += fprintf (fp, " %.3e", fm1->band_adj);
        char_count += fprintf (fp, " %.3e %.3e", fm1->amp_beat1_adj, fm1->amp_beat2_adj);
        char_count += fprintf (fp, " %.3e %.3e", fm1->amp_pct1_adj, fm1->amp_pct2_adj);
        char_count += fprintf (fp, " %d", fm1->slide);
        char_count += fprintf (fp, " %lld %lld", fm1->tot_frames, fm1->cur_frames);
        char_count += fprintf (fp, "\n       %d %.2f %.1f\n", fm1->steps, fm1->slide_time, fm1->fuzz);
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
    case 9:  // binaural step slide
    case 11:  // binaural vary slide
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
        char_count = fprintf (fp, "   bin %.3f    %+.3f   %.3f   %.3f\n", 
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
        char_count = fprintf (fp, "   noise %.3f   %.4f   %.3f   %d\n", 
                      noise1->carrier, AMP_DA (noise1->amp * amp_comp (noise1->carrier)), 
                      noise1->split_now, noise1->behave );
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
        char_count = fprintf (fp, "   once %lld   %lld   %lld   %.3f   %.3f\n", 
                      once1->sofar, once1->off1, once1->play, AMP_DA (once1->amp), once1->split_now );
        break;
      }
    case 8:  // chronaural
    case 10:  // chronaural step slide
    case 12:  // chronaural vary slide
      {
        chronaural *chronaural1;

        chronaural1 = (chronaural *) this;
        char_count += fprintf (fp, "   chron %.3f", chronaural1->carrier);
        char_count += fprintf (fp, "   %.3f", chronaural1->beat);
        char_count += fprintf (fp, "   %.3f", AMP_DA (chronaural1->amp * amp_comp (chronaural1->carrier)));
        char_count += fprintf (fp, "   %.3f", chronaural1->phase);
        char_count += fprintf (fp, "   %.3f", chronaural1->split_now);
        char_count += fprintf (fp, "   %.3e  %.3f\n", chronaural1->split_adj, chronaural1->split_beat); 
        break;
      }
    case 13:  // pulse
    case 14:  // pulse step slide
    case 15:  // pulse vary slide
      {
        pulse *pulse1;

        pulse1 = (pulse *) this;
        char_count += fprintf (fp, "   pulse %.3f", pulse1->carrier);
        char_count += fprintf (fp, "   %.3f", pulse1->beat);
        char_count += fprintf (fp, "   %.3f", AMP_DA (pulse1->amp * amp_comp (pulse1->carrier)));
        char_count += fprintf (fp, "   %.3f", pulse1->phase);
        char_count += fprintf (fp, "   %.3f", pulse1->time);
        char_count += fprintf (fp, "   %.3f", pulse1->split_now);
        char_count += fprintf (fp, "   %.3e  %.3f\n", pulse1->split_adj, pulse1->split_beat); 
        break;
      }
    case 16:  // phase
    case 17:  // phase step slide
    case 18:  // phase vary slide
      {
        double amp1, amp2;
        phase *phase1;

        phase1 = (phase *) this;  // reassign void pointer as phase struct
          /* use last calculated values instead of calculating new ones */
        if (opt_c)  // compensate
          amp1 = amp2 = (phase1->amp * amp_comp (phase1->carrier));
        else
          amp1 = amp2 = phase1->amp;
          /* perform the amplitude variation adjustment if required */
        if (phase1->amp_beat1 > 0.0)
          amp1 += ((amp1 * phase1->amp_pct1) * sin_table[phase1->amp_off1]);
        if (phase1->amp_beat2 > 0.0)
          amp2 += ((amp2 * phase1->amp_pct2) * sin_table[phase1->amp_off2]);
        char_count += fprintf (fp, "   phase %.3f  %+.3f   %.3f   %.3f", 
                      phase1->carrier, phase1->beat, AMP_DA (amp1), AMP_DA (amp2));
        char_count += fprintf (fp, "   %.3f\n", phase1->phase);
      }
      break;
    case 19:  // fm
    case 20:  // fm step slide
    case 21:  // fm vary slide
      {
        double amp1, amp2;
        fm *fm1;

        fm1 = (fm *) this;  // reassign void pointer as fm struct
          /* use last calculated values instead of calculating new ones */
        if (opt_c)  // compensate
          amp1 = amp2 = (fm1->amp * amp_comp (fm1->carrier));
        else
          amp1 = amp2 = fm1->amp;
          /* perform the amplitude variation adjustment if required */
        if (fm1->amp_beat1 > 0.0)
          amp1 += ((amp1 * fm1->amp_pct1) * sin_table[fm1->amp_off1]);
        if (fm1->amp_beat2 > 0.0)
          amp2 += ((amp2 * fm1->amp_pct2) * sin_table[fm1->amp_off2]);
        if (fm1->channel == 1)  // left channel only
          amp2 = 0.0;
        else if (fm1->channel == 2)  // right channel only
          amp1 = 0.0;
        char_count += fprintf (fp, "   fm %.3f  %+.3f   %.3f   %.3f", 
                      fm1->carrier, fm1->beat, AMP_DA (amp1), AMP_DA (amp2));
        char_count += fprintf (fp, "   %.3f\n", fm1->shift);
      }
      break;
    default:  // not known, do nothing
      ;
  }
  return char_count;
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

/*
*	Determine whether the audio_device supports the requested rate in hardware.
* If it doesn't, set the rate to nearest hardware rate supported.  This will 
* allow the generate_frames and resample function to use the correct
* rate before we open the sound card.  If plughw cannot be opened use the
* default device at a frame rate of 48000, the fixed rate of dmix.
*/

void
alsa_validate_device_and_rate ()
{	
  char *default_device = "default" ;
  //char *device = "plughw:0,0" ;
  char *device_to_use = NULL;
  unsigned val;
  unsigned samplerate = (unsigned) out_rate;
  int dir = 0;
	int err ;
  snd_pcm_t *alsa_dev;
	snd_pcm_info_t *info_params ;
	snd_pcm_hw_params_t *hw_params ;

  if (opt_b || opt_o || opt_w)  // writing to file, don't bother checking device and rate
    return;
  if (opt_a)  // audio device in options or configuration
    device_to_use = opt_a_plughw;
  else  // use default device
    device_to_use = default_device;

  err = snd_pcm_open (&alsa_dev, device_to_use, SND_PCM_STREAM_PLAYBACK, 0);
	if (err < 0)
	{	fprintf (stderr, "cannot open audio device \"%s\" (%s)\n", device_to_use, snd_strerror (err)) ;
		goto catch_error ;
		} ;

  if (!opt_a)  // no option or configuration audio plughw, have to create it from default
  {
    err = snd_pcm_info_malloc (&info_params);
    if (err < 0)
    {	fprintf (stderr, "cannot allocate information parameter structure (%s)\n", snd_strerror (err)) ;
      goto catch_error ;
      } ;

    err = snd_pcm_info (alsa_dev, info_params);  // get info on the default card
    if (err < 0)
    {	fprintf (stderr, "cannot get information for the default card (%s)\n", snd_strerror (err)) ;
      goto catch_error ;
      } ;
    if (!opt_q)  // not quiet
    {
          /* RO/WR (control): device number */
      fprintf (stderr, "Default device number (%u)\n", snd_pcm_info_get_device (info_params));
         /* RO/WR (control): subdevice number */
      fprintf (stderr, "Default subdevice number (%u)\n", snd_pcm_info_get_subdevice (info_params));
            /* RO/WR (control): stream number */
      fprintf (stderr, "Default stream number (%d)\n", snd_pcm_info_get_stream (info_params));
           /* R: card number */
      fprintf (stderr, "Default card number (%d)\n", snd_pcm_info_get_card (info_params));
         /* ID (user selectable) */
      fprintf (stderr, "Default id (%s)\n", snd_pcm_info_get_id (info_params));
         /* name of this device */
      fprintf (stderr, "Default name (%s)\n", snd_pcm_info_get_name (info_params));
        /* subdevice name */
      fprintf (stderr, "Default subname (%s)\n", snd_pcm_info_get_subdevice_name (info_params));
            /* SNDRV_PCM_CLASS_* */
      fprintf (stderr, "Default dev_class (%d)\n", snd_pcm_info_get_class (info_params));
         /* SNDRV_PCM_SUBCLASS_* */
      fprintf (stderr, "Default dev_subclass (%d)\n", snd_pcm_info_get_subclass (info_params));
      fprintf (stderr, "Default subdevices_count (%u)\n", snd_pcm_info_get_subdevices_count (info_params));
      fprintf (stderr, "Default subdevices_avail (%u)\n", snd_pcm_info_get_subdevices_avail (info_params));
    }
    err = snd_pcm_close (alsa_dev) ;  // close the device so we can create new direct plughw plugin
    if (err < 0)
    {	fprintf (stderr, "Could not close audio device \"%s\" (%s)\n", device_to_use, snd_strerror (err)) ;
      goto catch_error ;
      } ;

    char hw_from_default [32];
    int cardno = snd_pcm_info_get_card (info_params); 
    if (cardno < 0)  // If default is user defined, this is set to actual card.
      cardno = 0;  //  If not, dmix leaves as -1 and defaults to card 0 (look at id in info).
    int devno = snd_pcm_info_get_device (info_params);
    if (devno < 0)  // This appears to always be set, just here as insurance.
      devno = 0;
    int numchars = snprintf (hw_from_default, sizeof (hw_from_default), 
                                  "plughw:%d,%d", cardno, devno); 
    if (!opt_q)  // not quiet
      fprintf (stderr, "Plughw  %s  numchars %d\n", hw_from_default, numchars);
    /*  Now reopen and get feasible hardware parameters with plughw instead of default.
     *  This will allow bypassing dmix in order to set rates other than 48000.
     */
    err = snd_pcm_open (&alsa_dev, hw_from_default, SND_PCM_STREAM_PLAYBACK, 0);
    if (err < 0)
    {	fprintf (stderr, "cannot open audio device \"%s\" (%s)\n", hw_from_default, snd_strerror (err)) ;
      fprintf (stderr, "Using default device at 48000 frame rate\n") ;
      samplerate = out_rate = 48000;  // set rate to dmix rate
      strcpy (hw_from_default, default_device);  // set the device to default
      err = snd_pcm_open (&alsa_dev, default_device, SND_PCM_STREAM_PLAYBACK, 0);  // open default device
      if (err < 0)
      {	fprintf (stderr, "cannot open audio device \"%s\" (%s)\n", device_to_use, snd_strerror (err)) ;
        goto catch_error ;
      } ;
    } ;

    //snd_pcm_nonblock (alsa_dev, 0) ;  // 0 means block, 1 means nonblock, 0 is default
    snd_pcm_info_free (info_params) ;  // done with info
    /* Now that the default or plughw device opened successfully,
     * pretend that the default or plughw device was given 
     * as -a / --audio_device option so alsa_open can use it directly
     * and opens the same device that the rate came from */
    opt_a = 1;
    opt_a_plughw = StrDup (hw_from_default);
  }
  err = snd_pcm_hw_params_malloc (&hw_params);
	if (err < 0)
	{	fprintf (stderr, "cannot allocate hardware parameter structure (%s)\n", snd_strerror (err)) ;
		goto catch_error ;
		} ;

  err = snd_pcm_hw_params_any (alsa_dev, hw_params);
	if (err < 0)
	{	fprintf (stderr, "cannot initialize hardware parameter structure (%s)\n", snd_strerror (err)) ;
		goto catch_error ;
		} ;

  err = snd_pcm_hw_params_set_access (alsa_dev, hw_params, SND_PCM_ACCESS_RW_INTERLEAVED);
	if (err < 0)
	{	fprintf (stderr, "cannot set access type (%s)\n", snd_strerror (err)) ;
		goto catch_error ;
		} ;

  err = snd_pcm_hw_params_set_format (alsa_dev, hw_params, SND_PCM_FORMAT_FLOAT64);
	if (err < 0)
	{	fprintf (stderr, "cannot set sample format (%s)\n", snd_strerror (err)) ;
		goto catch_error ;
		} ;

  /* lock the sample rate to use only hardware
   * supported rates, avoid resampling
   */
  err = snd_pcm_hw_params_set_rate_resample (alsa_dev, hw_params, 0);
	if (err < 0)
	{	fprintf (stderr, "cannot block resample of sample rates (%s)\n", snd_strerror (err)) ;
		goto catch_error ;
		} ;

  err = snd_pcm_hw_params_set_rate_near (alsa_dev, hw_params, &samplerate, 0);
	if (err < 0)
	{	fprintf (stderr, "cannot set sample rate (%s)\n", snd_strerror (err)) ;
		goto catch_error ;
		} ;

  err = snd_pcm_hw_params_get_rate (hw_params, &val, &dir);
	if (err < 0)
  { fprintf (stderr, "cannot get nearest sample rate (%s)\n", snd_strerror (err));
		goto catch_error ;
		} ;
  
  if (out_rate != (int) val)  // if requested rate different than nearest hardware rate
    out_rate = (int) val;  // set the rate to the nearest hardware supported rate

	snd_pcm_hw_params_free (hw_params) ;

  err = snd_pcm_close (alsa_dev) ;  // close the device now that the correct plughw plugin and rate determined
  if (err < 0)
  {	fprintf (stderr, "Could not close audio device \"%s\" (%s)\n", device_to_use, snd_strerror (err)) ;
    goto catch_error ;
    } ;

catch_error :

	if (err < 0 && alsa_dev != NULL)
	{	snd_pcm_close (alsa_dev) ;
		} ;
} /* alsa_validate_device_and_rate */

/*------------------------------------------------------------------------------
**	Linux alsa functions for playing a sound.
*/

static snd_pcm_t *
alsa_open (snd_pcm_t *alsa_dev, int channels, unsigned samplerate, int realtime)
{	
  char *default_device = "default" ;
  //char *device = "plughw:0,0" ;
  char *device_to_use = NULL;
  unsigned val;
  unsigned long lval;
  int dir = 0;
	int err ;
	snd_pcm_info_t *info_params ;
	snd_pcm_hw_params_t *hw_params ;
	snd_pcm_uframes_t buffer_size, start_threshold ;
	snd_pcm_uframes_t alsa_period_size, alsa_buffer_frames ;
	snd_pcm_sw_params_t *sw_params ;

	if (realtime)
	{	alsa_period_size = 256 ;
		alsa_buffer_frames = 3 * alsa_period_size ;
		}
	else
	{	alsa_period_size = 1024 ;
		alsa_buffer_frames = 32 * alsa_period_size ;
		} ;

  if (opt_a)  // audio device in options or configuration
    device_to_use = opt_a_plughw;
  else  // use default device
    device_to_use = default_device;

  err = snd_pcm_open (&alsa_dev, device_to_use, SND_PCM_STREAM_PLAYBACK, 0);
	if (err < 0)
	{	fprintf (stderr, "cannot open audio device \"%s\" (%s)\n", device_to_use, snd_strerror (err)) ;
		goto catch_error ;
		} ;

  if (!opt_a)  // no option or configuration audio plughw, have to create it from default
  {
    err = snd_pcm_info_malloc (&info_params);
    if (err < 0)
    {	fprintf (stderr, "cannot allocate information parameter structure (%s)\n", snd_strerror (err)) ;
      goto catch_error ;
      } ;

    err = snd_pcm_info (alsa_dev, info_params);  // get info on the default card
    if (err < 0)
    {	fprintf (stderr, "cannot get information for the default card (%s)\n", snd_strerror (err)) ;
      goto catch_error ;
      } ;
    if (!opt_q)  // not quiet
    {
          /* RO/WR (control): device number */
      fprintf (stderr, "Default device number (%u)\n", snd_pcm_info_get_device (info_params));
         /* RO/WR (control): subdevice number */
      fprintf (stderr, "Default subdevice number (%u)\n", snd_pcm_info_get_subdevice (info_params));
            /* RO/WR (control): stream number */
      fprintf (stderr, "Default stream number (%d)\n", snd_pcm_info_get_stream (info_params));
           /* R: card number */
      fprintf (stderr, "Default card number (%d)\n", snd_pcm_info_get_card (info_params));
         /* ID (user selectable) */
      fprintf (stderr, "Default id (%s)\n", snd_pcm_info_get_id (info_params));
         /* name of this device */
      fprintf (stderr, "Default name (%s)\n", snd_pcm_info_get_name (info_params));
        /* subdevice name */
      fprintf (stderr, "Default subname (%s)\n", snd_pcm_info_get_subdevice_name (info_params));
            /* SNDRV_PCM_CLASS_* */
      fprintf (stderr, "Default dev_class (%d)\n", snd_pcm_info_get_class (info_params));
         /* SNDRV_PCM_SUBCLASS_* */
      fprintf (stderr, "Default dev_subclass (%d)\n", snd_pcm_info_get_subclass (info_params));
      fprintf (stderr, "Default subdevices_count (%u)\n", snd_pcm_info_get_subdevices_count (info_params));
      fprintf (stderr, "Default subdevices_avail (%u)\n", snd_pcm_info_get_subdevices_avail (info_params));
    }
    err = snd_pcm_close (alsa_dev) ;  // close the device so we can create new direct plughw plugin
    if (err < 0)
    {	fprintf (stderr, "Could not close audio device \"%s\" (%s)\n", device_to_use, snd_strerror (err)) ;
      goto catch_error ;
      } ;

    char hw_from_default [32];
    int cardno = snd_pcm_info_get_card (info_params); 
    if (cardno < 0)  // If default is user defined, this is set to actual card.
      cardno = 0;  //  If not, dmix leaves as -1 and defaults to card 0 (look at id in info).
    int devno = snd_pcm_info_get_device (info_params);
    if (devno < 0)  // This appears to always be set, just here as insurance.
      devno = 0;
    int numchars = snprintf (hw_from_default, sizeof (hw_from_default), 
                                  "plughw:%d,%d", cardno, devno); 
    if (!opt_q)  // not quiet
      fprintf (stderr, "Plughw  %s  numchars %d\n", hw_from_default, numchars);
    /*  Now reopen and get feasible hardware parameters with plughw instead of default.
     *  This will allow bypassing dmix in order to set higher rates than 48000.
     */
    // snd_pcm_nonblock (alsa_dev, 1) ;  // 0 means block, 1 means nonblock, 0 is default
    err = snd_pcm_open (&alsa_dev, hw_from_default, SND_PCM_STREAM_PLAYBACK, 0);
    if (err < 0)
    {	fprintf (stderr, "cannot open audio device \"%s\" (%s)\n", hw_from_default, snd_strerror (err)) ;
      goto catch_error ;
      } ;

    snd_pcm_info_free (info_params) ;  // done with info
  }
  err = snd_pcm_hw_params_malloc (&hw_params);
	if (err < 0)
	{	fprintf (stderr, "cannot allocate hardware parameter structure (%s)\n", snd_strerror (err)) ;
		goto catch_error ;
		} ;

  err = snd_pcm_hw_params_any (alsa_dev, hw_params);
	if (err < 0)
	{	fprintf (stderr, "cannot initialize hardware parameter structure (%s)\n", snd_strerror (err)) ;
		goto catch_error ;
		} ;

  if (!opt_q)  // not quiet
  {
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
  }

  err = snd_pcm_hw_params_set_access (alsa_dev, hw_params, SND_PCM_ACCESS_RW_INTERLEAVED);
	if (err < 0)
	{	fprintf (stderr, "cannot set access type (%s)\n", snd_strerror (err)) ;
		goto catch_error ;
		} ;

#if NOTDEFINED
  int iformat;
  fprintf (stderr, "Value of last format %lu\n", 
                          (unsigned long) SND_PCM_FORMAT_LAST) ;
  for (iformat = 0; iformat <= SND_PCM_FORMAT_LAST; iformat++)
  {
    err = snd_pcm_hw_params_test_format (alsa_dev, hw_params, iformat);
    if (err < 0)
      fprintf (stderr, "test of sample format %lu failed (%s)\n", 
                          (unsigned long) iformat, snd_strerror (err)) ;
  }
#endif  // NOTDEFINED

  err = snd_pcm_hw_params_set_format (alsa_dev, hw_params, SND_PCM_FORMAT_FLOAT64);
	if (err < 0)
	{	fprintf (stderr, "cannot set sample format %lu (%s)\n", 
                        (unsigned long) SND_PCM_FORMAT_FLOAT64, snd_strerror (err)) ;
		goto catch_error ;
		} ;

#if NOTDEFINED
  snd_pcm_format_t fval;
  snd_pcm_hw_params_get_format (hw_params, &fval);
  fprintf (stderr, "Format (%lu)\n", (unsigned long) fval);
  if ((unsigned long) fval != (unsigned long) SND_PCM_FORMAT_FLOAT64)
    fprintf (stderr, "Format (%lu) differs from requested (%lu)\n", 
              (unsigned long) fval, (unsigned long) SND_PCM_FORMAT_FLOAT64);
#endif  // NOTDEFINED

  /* lock the sample rate to use only hardware
   * supported rates, avoid resampling
   */
  err = snd_pcm_hw_params_set_rate_resample (alsa_dev, hw_params, 0);
	if (err < 0)
	{	fprintf (stderr, "cannot block resample of sample rates (%s)\n", snd_strerror (err)) ;
		goto catch_error ;
		} ;

  err = snd_pcm_hw_params_set_rate_near (alsa_dev, hw_params, &samplerate, 0);
	if (err < 0)
	{	fprintf (stderr, "cannot set sample rate (%s)\n", snd_strerror (err)) ;
		goto catch_error ;
		} ;

  err = snd_pcm_hw_params_set_channels (alsa_dev, hw_params, channels);
	if (err < 0)
	{	fprintf (stderr, "cannot set channel count (%s)\n", snd_strerror (err)) ;
		goto catch_error ;
		} ;

  err = snd_pcm_hw_params_set_buffer_size_near (alsa_dev, hw_params, &alsa_buffer_frames);
	if (err < 0)
	{	fprintf (stderr, "cannot set buffer size (%s)\n", snd_strerror (err)) ;
		goto catch_error ;
		} ;

  err = snd_pcm_hw_params_set_period_size_near (alsa_dev, hw_params, &alsa_period_size, 0);
	if (err < 0)
	{	fprintf (stderr, "cannot set period size (%s)\n", snd_strerror (err)) ;
		goto catch_error ;
		} ;

  err = snd_pcm_hw_params (alsa_dev, hw_params);
	if (err < 0)
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
  if (!opt_q)  // not quiet
  {
    snd_pcm_hw_params_get_rate (hw_params, &val, &dir);
    fprintf (stderr, "Actual rate (%u)  Direction = %d\n", val, dir);
    snd_pcm_hw_params_get_channels (hw_params, &val);
    fprintf (stderr, "Actual channels (%u)\n", val);
    snd_pcm_hw_params_get_period_size (hw_params, &lval, &dir);
    fprintf (stderr, "Actual period_size (%lu)  Direction = %d\n", lval, dir);
    snd_pcm_hw_params_get_buffer_size (hw_params, &lval);
    fprintf (stderr, "Actual buffer_size (%lu)\n", lval);
  }

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

/* Threaded version of alsa write function, args in passed structure.
 * Try to eliminate problem with alsa blocking failing using threads
 * by calling an intermediate function. */
void
alsa_write (void *call_parms)
{	
  /* extract calling parameters from passed structure */
  slice *sound_slice = (slice *) call_parms;
  snd_pcm_t *alsa_dev = sound_slice->alsa_dev;
  double *data = sound_slice->buffer;
  int frames = sound_slice->frames;
  int channels = sound_slice->channels;

    /* send doubles to alsa-lib to translate to sound card format and play */
  alsa_write_retval = alsa_write_double (alsa_dev, data, frames, channels) ;

  pthread_mutex_unlock (&mtx_play);  // allow main to call again, locked in play_loop
} /* alsa_write */

static int
alsa_write_double (snd_pcm_t *alsa_dev, double *data, int frames, int channels)
{	static	int epipe_count = 0 ;

	snd_pcm_status_t *status ;
  struct timespec time_to_wait, time_left; 
	int total = 0 ;
	int retval ;
	int wait_retval ;

	if (epipe_count > 0)
		epipe_count -- ;

	while (total < frames)
  {	
    retval = snd_pcm_writei (alsa_dev, (data + (total * channels)), (frames - total)) ;
		if (retval >= 0)
		{	total += retval ;
			if (total == frames)
				return total ;
      else
      {
        int frames_left = frames - total;  // all the frames didn't get written, how many are left to write?
        double time_for_frames = (double) frames_left / (double) out_rate;  // how long to play that many frames?
        long nanoseconds = floor ((time_for_frames * 1000000.));  // how many nanoseconds is that?
        time_to_wait.tv_sec = 0;  // buffer size less than second
        time_to_wait.tv_nsec = nanoseconds;  // set the nanoseconds
        wait_retval = nanosleep (&time_to_wait, &time_left);  // wait for that many nanoseconds
        if (wait_retval < 0)  // an error occurred, zero if no error
        { 
          switch (wait_retval)
          { 
            case -EFAULT :
							fprintf (stderr, "nanosleep: execution fault\n") ;
              continue ;
              break ;
            case -EINTR :
							fprintf (stderr, "nanosleep: signal interrupt with %ld nanoseconds left\n", time_left.tv_nsec) ;
              continue ;
              break ;
            default :
              fprintf (stderr, "nanosleep: unknown error wait_retval = %d\n", wait_retval) ;
              continue ;
              break ;
          } ; /* nanosleep switch */
        }
      }
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

/* Simpler threaded version of file write function, args in passed structure.
 * Try to eliminate problem with alsa blocking failing using threads
 * by calling an intermediate function. */
void
file_write (void *call_parms)
{	
  /* extract calling parameters from passed structure */
  slice *sound_slice = (slice *) call_parms;
  SNDFILE * sndfile = sound_slice->sndfile;
  double *write_buffer = sound_slice->buffer;
  int offset = sound_slice->frames;

        /* writing from a double */
  offset = sf_writef_double (sndfile, write_buffer, offset);

  // allow main to call again, locked by save_loop
  pthread_mutex_unlock (&mtx_write);
} /* file_write */

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

