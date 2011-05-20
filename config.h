/* Config file for xscreensaver, Copyright (c) 1991-1997 Jamie Zawinski.
 *
 * This file is included by the various Imakefiles.
 * After editing this file, you need to execute the commands
 *
 *         xmkmf
 *         make Makefiles
 *         make depend
 *
 * in the top-level xscreensaver directory, or your changes to this
 * file may not take effect.
 */


/*  Uncomment the following line if gettimeofday() on your system requres
 *  two arguments.  It's pretty much a crap shoot whether it does; if you
 *  don't know, try it and see if you get compilation errors.
 */
/* #define GETTIMEOFDAY_TWO_ARGS */


/*  Uncomment the following line if you have the XPM library installed.
 *  Some of the demos can make use of this if it is available.
 */
#define HAVE_XPM


/*  Uncomment the following line if you don't have Motif.  If you don't have
 *  Motif, then the abominable Athena widgets will be used instead.  Most of
 *  the functionality will be present, but it will look much uglier than if
 *  you use Motif.  (I'm told that LessTif works as well.)
 */
/* #define NO_MOTIF */


/*  Uncomment the following line if you have OpenGL.  Some of the included
 *  screen hacks depend on it.  (If you don't have it, you'll simply miss
 *  out on a few of the demos.)  If you define this, make sure you go and
 *  add the programs to the app-defaults file as well, as they're not 
 *  included in the programs resource by default (since they're not built
 *  by default.)
 */
/* #define HAVE_GL */

/*  Define this if the variant of GL that you have is MesaGL, rather than
 *  the real OpenGL (the library names are different.)
 */
/* #define HAVE_MESAGL */


/*  Uncomment the following line if for some reason the locking code doesn't
 *  work (for example, if you don't have the crypt() system call, or if you
 *  don't use standard passwd files.)  If you need to do this, please let me
 *  know.
 *
 *  I'm told that locking doesn't work for sites which run AFS.  I don't know
 *  anything about how one codes authentication for AFS; if you do, please let
 *  me know...
 */
/* #define NO_LOCKING */


/*  Select supported server extensions.  First, some background:
 *  There are three distinct server extensions which are useful with 
 *  XScreenSaver: XIDLE, MIT-SCREEN-SAVER, and SCREEN_SAVER.
 *
 *  The XIDLE extension resides in .../contrib/extensions/xidle/ on the X11R5
 *  contrib tape.  This extension lets the client get accurate idle-time 
 *  information from the X server in a potentially more reliable way than by
 *  simply watching for keyboard and mouse activity.  However, the XIDLE 
 *  extension has apparently not been ported to X11R6.
 *
 *  The SCREEN_SAVER extension is found (as far as I know) only in the SGI
 *  X server, and it exists in all releases since (at least) Irix 5.  The
 *  relevant header file is /usr/include/X11/extensions/XScreenSaver.h.
 *
 *  The similarly-named MIT-SCREEN-SAVER extension came into existence long
 *  after the SGI SCREEN_SAVER extension was already in use, and resides in
 *  .../contrib/extensions/screensaver/ on the X11R6 contrib tape.  It is
 *  also found in certain recent X servers built in to NCD X terminals.
 *
 *     The MIT extension does basically the same thing that the XIDLE extension
 *     does, but there are two things wrong with it: first, because of the way
 *     the extension was designed, the `fade' option to XScreenSaver will be
 *     uglier: just before the screen fades out, there will be an unattractive
 *     flicker to black, because this extension blanks the screen *before*
 *     telling us that it is time to do so.  Second, this extension is known to
 *     be buggy; on the systems I use, it works, but some people have reported
 *     X server crashes as a result of using it.  XScreenSaver uses this
 *     extension rather conservatively, because when I tried to use any of its
 *     more complicated features, I could get it to crash the server at the
 *     drop of a hat.
 *
 *     In short, the MIT-SCREEN-SAVER extension is a piece of junk.  The older
 *     SGI SCREEN_SAVER extension works great, as does XIDLE.  It would be nice
 *     If those two existed on more systems, that is, would be adopted by the
 *     X Consortium in favor of their inferior "not-invented-here" entry.
 */

/*  Uncomment the following line if you have the XIDLE extension installed.
 *  If you have the XIDLE extension, this is recommended.  (You have this
 *  extension if the file /usr/include/X11/extensions/xidle.h exists.)
 *  Turning on this flag lets XScreenSaver work better with servers which 
 *  support this extension; but it will still work with servers which do not 
 *  suport it, so it's a good idea to compile in support for it if you can.
 */
/* #define HAVE_XIDLE_EXTENSION */

/*  Uncomment the following line if you have the MIT-SCREEN-SAVER extension
 *  installed.  This is NOT RECOMMENDED.  See the caveats about this extension,
 *  above.  (It's available if the file /usr/include/X11/extensions/scrnsaver.h
 *  exists.)
 */
/* #define HAVE_MIT_SAVER_EXTENSION */


/*  Use the following line if you have the SGI SCREEN_SAVER extension; the
 *  default below should be correct (use it if and only if running on an SGI.)
 *  Compiling in support for this extension is recommended, if at all possible.
 */
#ifdef SGIArchitecture
# define HAVE_SGI_SAVER_EXTENSION
#endif


/*  Uncomment the following line if your system doesn't have the select()
 *  system call.  If you need to do this, please let me know.  (I don't really
 *  think that any such systems exist in this day and age...)
 */
/* #define NO_SELECT */


/*  Uncomment the following line if your system doesn't have the setuid(),
 *  setregid(), and getpwnam() library routines.
 *
 *  WARNING: if you do this, it will be unsafe to run xscreensaver as root
 *  (which probably means you can't have it be started by xdm.)  If you are
 *  on such a system, please try to find the corresponding way to do this,
 *  and then tell me what it is.
 */
/* #define NO_SETUID */

/*  Uncomment the following line if you want to use kerberos authentication
 *  to lock/unlock the screen instead of your local password. This currently
 *  uses Kerberos V4, but a V5 server with V4 compatibility will work.
 *  WARNING: DO NOT USE AFS string-to-key passwords with this option. This
 *  option currently *only* works with standard Kerberos des_string_to_key.
 *  If your password is an AFS password and not a kerberos password, it will
 *  not authenticate properly. See the comments in driver/kpasswd.c for more
 *  information if you need it. 
 */
/* #define USE_KERBEROS */

/*  Uncomment the following line if your system uses `shadow' passwords,
 *  that is, the passwords live in /etc/shadow instead of /etc/passwd,
 *  and one reads them with getspnam() instead of getpwnam().  (Note that
 *  SCO systems do some random other thing; others might as well.  See the
 *  ifdefs in driver/passwd.c if you're having trouble related to reading
 *  passwords.)
 */
/* #define HAVE_SHADOW */

/* Uncomment the following line if your system is Digital Unix with
   so-called ``Enhanced Security'', that is, the passwords live in
   /tcb/files/auth/<initial>/<username> instead of in /etc/passwd,
 * and one reads them with getprpwnam() instead of getpwnam().
 */
/* #define HAVE_DEC_ENHANCED */

/* Uncomment the following line if your system is Solaris with ``adjunct''
   passwords (this is the version where one gets at the passwords with
   getpwanam() instead of getpwnam().)  I haven't tested this one, let
   me know if it works.
 */
/* #define HAVE_ADJUNCT_PASSWD */

/* Uncomment the following line if you are running HPUX with so-called
   ``Secure Passwords'' (if you have /usr/include/hpsecurity.h, you probably
   have this.)  I haven't tested this one, let me know if it works.
 */
/* #define HAVE_HPUX_PASSWD */


/* Define this if you have the XReadDisplay extension (I think this is an
   SGI-only thing; it's in <X11/extensions/readdisplay.h>.)  A couple of
   the screenhacks will take advantage of this if it's available.
 */
#ifdef SGIArchitecture
# define HAVE_READ_DISPLAY_EXTENSION
#endif


/*  You may need to edit these to correspond to where Motif is installed,
 *  if your site has Motif installed in a nonstandard place.
 */
#ifndef NO_MOTIF
  MOTIFINCLUDES = -I/usr/local/include/
 MOTIFLDOPTIONS = -L/usr/local/lib/
      MOTIFLIBS = -lXm
#endif


/*  On some systems, only programs running as root can use the getpwent()
    library routine.  This means that, in order for locking to work, the
    screensaver must be installed as setuid to root.  Define this to make
    that happen.  (You must run "make install" as root for it to work.)
    (If your system needs this, and the default below is not correct,
    please let me know.)
 */
#if defined(HPArchitecture) || defined(AIXArchitecture) || \
    defined(HAVE_SHADOW) || defined(NetBSDArchitecture) || \
    defined(HAVE_DEC_ENHANCED) || defined(HAVE_ADJUNCT_PASSWD) || \
    defined(HAVE_HPUX_PASSWD)
# define INSTALL_SETUID
#endif

#ifdef HPArchitecture
      CCOPTIONS = -Aa -D_HPUX_SOURCE	/* eat me */
# if (ProjectX <= 4)
  MOTIFINCLUDES = -I/usr/include/Motif1.1
 MOTIFLDOPTIONS = -L/usr/lib/Motif1.1
# else /* R5 */
  MOTIFINCLUDES = -I/usr/include/Motif1.2
 MOTIFLDOPTIONS = -L/usr/lib/Motif1.2
# endif /* R5 */
#endif /* HPArchitecture */

#ifdef MacIIArchitecture
      CCOPTIONS = -D_POSIX_SOURCE
#endif /* MacIIArchitecture */

#if (ProjectX <= 4)
# define R5ISMS -DXPointer="char*"
#else /* r5 or better */
# define R5ISMS
#endif

#if defined(HAVE_MESAGL) && !defined(HAVE_GL)
# define HAVE_GL
#endif

/* It seems that some versions of Sun's dynamic X libraries are broken; if
   you get link errors about _get_wmShellWidgetClass being undefined, try
   adding -Bstatic to the link command.
 */