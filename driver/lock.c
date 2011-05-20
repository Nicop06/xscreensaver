/*    xscreensaver, Copyright (c) 1993-1997 Jamie Zawinski <jwz@netscape.com>
 *
 * Permission to use, copy, modify, distribute, and sell this software and its
 * documentation for any purpose is hereby granted without fee, provided that
 * the above copyright notice appear in all copies and that both that
 * copyright notice and this permission notice appear in supporting
 * documentation.  No representations are made about the suitability of this
 * software for any purpose.  It is provided "as is" without express or 
 * implied warranty.
 */

/* Athena locking code contributed by Jon A. Christopher <jac8782@tamu.edu> */
/* Copyright 1997, with the same permissions as above. */

#ifndef NO_LOCKING

#ifdef __STDC__
# include <stdlib.h>
# include <unistd.h>
# include <string.h>
#endif

#ifdef  HAVE_SHADOW
# include <shadow.h>
#endif

#ifdef HAVE_DEC_ENHANCED
# include <sys/types.h>
# include <sys/security.h>
# include <prot.h>
#endif

#include <pwd.h>
#include <stdio.h>

#include <X11/Intrinsic.h>

#include "xscreensaver.h"

extern char *screensaver_version;
extern char *progname;
extern XtAppContext app;
extern Bool verbose_p;

#ifdef SCO
/* SCO has some kind of goofy, nonstandard security crap.  This stuff was
   donated by one of their victims, I mean users, Didier Poirot <dp@chorus.fr>.
 */
# include <sys/security.h>
# include <sys/audit.h>
# include <prot.h>
#endif

#ifndef __STDC__
# define _NO_PROTO
#endif

#ifdef NO_MOTIF

# include <X11/Shell.h>
# include <X11/StringDefs.h>
# include <X11/Xaw/Text.h>
# include <X11/Xaw/Label.h>
# include <X11/Xaw/Dialog.h>

static void passwd_done_cb ();
static XtActionsRec actionsList[] =
{
    {"passwdentered", (XtActionProc) passwd_done_cb},
};

static char Translations[] =
"\
<Key>Return:   passwdentered()\
";

#else /* Motif */

# include <Xm/Xm.h>
# include <Xm/List.h>
# include <Xm/TextF.h>

#endif /* Motif */

Time passwd_timeout;

extern Widget passwd_dialog;
extern Widget passwd_form;
extern Widget roger_label;
extern Widget passwd_label1;
extern Widget passwd_label3;
extern Widget passwd_text;
extern Widget passwd_done;
extern Widget passwd_cancel;

extern create_passwd_dialog P((Widget));
extern void ungrab_keyboard_and_mouse P((void));

static enum { pw_read, pw_ok, pw_fail, pw_cancel, pw_time } passwd_state;
#define PASSWDLEN 80
static char typed_passwd [PASSWDLEN];

static char root_passwd [255];
static char user_passwd [255];

#ifdef HAVE_SHADOW
# define PWTYPE struct spwd *
# define PWSLOT sp_pwdp
# define GETPW  getspnam
#elif HAVE_DEC_ENHANCED
# define PWTYPE struct pr_passwd *
# define PWSLOT ufld.fd_encrypt
# define GETPW  getprpwnam
#else
# define PWTYPE struct passwd *
# define PWSLOT pw_passwd
# define GETPW  getpwnam
#endif

#ifdef SCO
# define PRPWTYPE struct pr_passwd *
# define GETPRPW getprpwnam
#endif

#ifdef NO_MOTIF
 Widget passwd_dialog;
 Widget passwd_form;
 Widget roger_label;
 Widget passwd_label1;
 Widget passwd_label3;
 Widget passwd_text;
 Widget passwd_done;
 Widget passwd_cancel;
 static void focus_fuckus P((Widget));
#endif /* NO_MOTIF */


Bool
lock_init P((int argc, char **argv))
{
  Bool ok = True;
  char *u;
  PWTYPE p;
#ifdef SCO
  PRPWTYPE prpwd;
#endif /* SCO */

#ifdef HAVE_DEC_ENHANCED      /* from M.Matsumoto <matsu@yao.sharp.co.jp> */
  set_auth_parameters(argc, argv);
  check_auth_parameters();
#endif /* HAVE_DEC_ENHANCED */

  p = GETPW ("root");

#ifdef SCO
  prpwd = GETPRPW ("root");
  if (prpwd && *prpwd->ufld.fd_encrypt)
    strcpy (root_passwd, prpwd->ufld.fd_encrypt);
#else /* !SCO */
  if (p && p->PWSLOT && p->PWSLOT[0] != '*')
    strcpy (root_passwd, p->PWSLOT);
#endif /* !SCO */
  else
    {
      fprintf (stderr, "%s: couldn't get root's password\n", progname);
      strcpy (root_passwd, "*");
    }

  /* It has been reported that getlogin() returns the wrong user id on some
     very old SGI systems... */
  u = (char *) getlogin ();
  if (u)
    {
#ifdef SCO
      prpwd = GETPRPW (u);
#endif /* SCO */
      p = GETPW (u);
    }
  else
    {
      /* getlogin() fails if not attached to a terminal;
	 in that case, use getpwuid(). */
      struct passwd *p2 = getpwuid (getuid ());
      u = p2->pw_name;
#ifdef HAVE_SHADOW
      p = GETPW (u);
#else
      p = p2;
#endif
    }

#ifdef SCO
  if (prpwd && *prpwd->ufld.fd_encrypt)
    strcpy (user_passwd, prpwd->ufld.fd_encrypt);
#else /* !SCO */
  if (p && p->PWSLOT &&
      /* p->PWSLOT[0] != '*' */		/* sensible */
      (strlen (p->PWSLOT) > 4)		/* solaris */
      )
    strcpy (user_passwd, p->PWSLOT);
#endif /* !SCO */
  else
    {
      fprintf (stderr, "%s: couldn't get password of \"%s\"\n", progname, u);
      strcpy (user_passwd, "*");
      ok = False;
    }
  return ok;
}



#if defined(NO_MOTIF) || (XmVersion >= 1002)
   /* The `destroy' bug apears to be fixed as of Motif 1.2.1, but
      the `verify-callback' bug is still present. */
# define DESTROY_WORKS
#endif

static void
#ifdef __STDC__
passwd_cancel_cb (Widget button, XtPointer client_data, XtPointer call_data)
#else /* ! __STDC__ */
passwd_cancel_cb (button, client_data, call_data)
     Widget button;
     XtPointer client_data, call_data;
#endif /* ! __STDC__ */
{
  passwd_state = pw_cancel;
}

static void
#ifdef __STDC__
passwd_done_cb (Widget button, XtPointer client_data, XtPointer call_data)
#else /* ! __STDC__ */
passwd_done_cb (button, client_data, call_data)
     Widget button;
     XtPointer client_data, call_data;
#endif /* ! __STDC__ */
{
  if (passwd_state != pw_read) return; /* already done */
#ifdef NO_MOTIF
  strncpy(typed_passwd, XawDialogGetValueString(passwd_form), PASSWDLEN);
#endif /* NO_MOTIF */
  if (!strcmp ((char *) crypt (typed_passwd, user_passwd), user_passwd))
    passwd_state = pw_ok;
  /* do not allow root to have empty passwd */
  else if (typed_passwd [0] &&
	   !strcmp ((char *) crypt (typed_passwd, root_passwd), root_passwd))
    passwd_state = pw_ok;
  else
    passwd_state = pw_fail;
}

#if !defined(NO_MOTIF) && defined(VERIFY_CALLBACK_WORKS)

  /* ####  It looks to me like adding any modifyVerify callback causes
     ####  Motif 1.1.4 to free the the TextF_Value() twice.  I can't see
     ####  the bug in the Motif source, but Purify complains, even if
     ####  check_passwd_cb() is a no-op.

     ####  Update: Motif 1.2.1 also loses, but in a different way: it
     ####  writes beyond the end of a malloc'ed block in ModifyVerify().
     ####  Probably this block is the text field's text.
   */

static void 
#ifdef __STDC__
check_passwd_cb (Widget button, XtPointer client_data, XtPointer call_data)
#else /* ! __STDC__ */
check_passwd_cb (button, client_data, call_data)
     Widget button;
     XtPointer client_data, call_data;
#endif /* ! __STDC__ */
{
  XmTextVerifyCallbackStruct *vcb = (XmTextVerifyCallbackStruct *) call_data;

  if (passwd_state != pw_read)
    return;
  else if (vcb->reason == XmCR_ACTIVATE)
    {
      passwd_done_cb (0, 0, 0);
    }
  else if (vcb->text->length > 1)	/* don't allow "paste" operations */
    {
      vcb->doit = False;
    }
  else if (vcb->text->ptr != 0)
    {
      int i;
      strncat (typed_passwd, vcb->text->ptr, vcb->text->length);
      typed_passwd [vcb->endPos + vcb->text->length] = 0;
      for (i = 0; i < vcb->text->length; i++)
	vcb->text->ptr [i] = '*';
    }
}

#else /* !VERIFY_CALLBACK_WORKS */

static void keypress P((Widget w, XEvent *event, String *av, Cardinal *ac));
static void backspace P((Widget w, XEvent *event, String *av, Cardinal *ac));
static void kill_line P((Widget w, XEvent *event, String *av, Cardinal *ac));
static void done P((Widget w, XEvent *event, String *av, Cardinal *ac));

static XtActionsRec actions[] = {{"keypress",  keypress},
				 {"backspace", backspace},
				 {"kill_line", kill_line},
				 {"done",      done}
			        };

#ifndef NO_MOTIF
#if 0 /* oh fuck, why doesn't this work? */
static char translations[] = "\
<Key>BackSpace:		backspace()\n\
<Key>Delete:		backspace()\n\
Ctrl<Key>H:		backspace()\n\
Ctrl<Key>U:		kill_line()\n\
Ctrl<Key>X:		kill_line()\n\
Ctrl<Key>J:		done()\n\
Ctrl<Key>M:		done()\n\
<Key>:			keypress()\n\
";
#else
static char translations[] = "<Key>:keypress()";
#endif
#endif /* Motif */

static void
#ifdef __STDC__
text_field_set_string (Widget widget, char *text, int position)
#else /* ! __STDC__ */
text_field_set_string (widget, text, position)
     Widget widget;
     char *text;
     int position;
#endif /* ! __STDC__ */
{
#ifdef NO_MOTIF
  char *buf;
  int endPos;

  XawTextBlock block;
  block.firstPos = 0;
  block.length = strlen (text);
  block.ptr = text;
  block.format = 0;
  if (block.length == 0)
    {
      buf=XawDialogGetValueString(passwd_form);
      if (buf)
	endPos=strlen(buf);
      else
	endPos=-1;
    }
  XawTextReplace (widget, 0, endPos, &block);
  XawTextSetInsertionPoint (widget, position);
#else  /* !NO_MOTIF */
  XmTextFieldSetString (widget, text);
  XmTextFieldSetInsertionPosition (widget, position);
#endif /* !NO_MOTIF */
}


static void
#ifdef __STDC__
keypress (Widget w, XEvent *event, String *argv, Cardinal *argc)
#else /* ! __STDC__ */
keypress (w, event, argv, argc)
     Widget w;
     XEvent *event;
     String *argv;
     Cardinal *argc;
#endif /* ! __STDC__ */
{
  int i, j;
  char s [sizeof (typed_passwd)];
  int size = XLookupString ((XKeyEvent *) event, s, sizeof (s), 0, 0);
  if (size != 1) return;

  /* hack because I can't get translations to dance to my tune... */
  if (*s == '\010') { backspace (w, event, argv, argc); return; }
  if (*s == '\177') { backspace (w, event, argv, argc); return; }
  if (*s == '\025') { kill_line (w, event, argv, argc); return; }
  if (*s == '\030') { kill_line (w, event, argv, argc); return; }
  if (*s == '\012') { done (w, event, argv, argc); return; }
  if (*s == '\015') { done (w, event, argv, argc); return; }

  i = j = strlen (typed_passwd);
  typed_passwd [i] = *s;
  s [++i] = 0;
  while (i--)
    s [i] = '*';

  text_field_set_string (passwd_text, s, j + 1);
}

static void
#ifdef __STDC__
backspace (Widget w, XEvent *event, String *argv, Cardinal *argc)
#else /* ! __STDC__ */
backspace (w, event, argv, argc)
     Widget w;
     XEvent *event;
     String *argv;
     Cardinal *argc;
#endif /* ! __STDC__ */
{
  char s [sizeof (typed_passwd)];
  int i = strlen (typed_passwd);
  int j = i;
  if (i == 0)
    return;
  typed_passwd [--i] = 0;
  s [i] = 0;
  while (i--)
    s [i] = '*';

  text_field_set_string (passwd_text, s, j + 1);
}

static void
#ifdef __STDC__
kill_line (Widget w, XEvent *event, String *argv, Cardinal *argc)
#else /* ! __STDC__ */
kill_line (w, event, argv, argc)
     Widget w;
     XEvent *event;
     String *argv;
     Cardinal *argc;
#endif /* ! __STDC__ */
{
  memset (typed_passwd, 0, sizeof (typed_passwd));
  text_field_set_string (passwd_text, "", 0);
}

static void
#ifdef __STDC__
done (Widget w, XEvent *event, String *argv, Cardinal *argc)
#else /* ! __STDC__ */
done (w, event, argv, argc)
     Widget w;
     XEvent *event;
     String *argv;
     Cardinal *argc;
#endif /* ! __STDC__ */
{
  passwd_done_cb (w, 0, 0);
}

#endif /* !VERIFY_CALLBACK_WORKS || NO_MOTIF */

static void
#ifdef __STDC__
format_into_label (Widget widget, char *string)
#else /* ! __STDC__ */
format_into_label (widget, string)
     Widget widget;
     char *string;
#endif /* ! __STDC__ */
{
  char *label = 0;
  char buf [255];
  Arg av[10];
  int ac = 0;

#ifdef NO_MOTIF
  XtVaGetValues (widget, XtNlabel, &label, 0);
#else  /* Motif */
  XmString xm_label = 0;
  XmString new_xm_label;
  XtSetArg (av [ac], XmNlabelString, &xm_label); ac++;
  XtGetValues (widget, av, ac);
  XmStringGetLtoR (xm_label, XmSTRING_DEFAULT_CHARSET, &label);
#endif /* Motif */

  if (!label || !strcmp (label, XtName (widget)))
    strcpy (buf, "ERROR: RESOURCES ARE NOT INSTALLED CORRECTLY");
  else
    sprintf (buf, label, string);

  ac = 0;
#ifdef NO_MOTIF
  XtSetArg (av [ac], XtNlabel, buf); ac++;
#else  /* Motif */
  new_xm_label = XmStringCreate (buf, XmSTRING_DEFAULT_CHARSET);
  XtSetArg (av [ac], XmNlabelString, new_xm_label); ac++;
#endif /* Motif */

  XtSetValues (widget, av, ac);
#ifndef NO_MOTIF
  XmStringFree (new_xm_label);
  XtFree (label);
#endif
}

#ifdef __STDC__
extern void skull (Display *, Window, GC, GC, int, int, int, int);
#endif

static void
#ifdef __STDC__
roger (Widget button, XtPointer client_data, XtPointer call_data)
#else /* ! __STDC__ */
roger (button, client_data, call_data)
     Widget button;
     XtPointer client_data, call_data;
#endif /* ! __STDC__ */
{
  Display *dpy = XtDisplay (button);
  Screen *screen = XtScreen (button);
  Window window = XtWindow (button);
  Arg av [10];
  int ac = 0;
  XGCValues gcv;
  Colormap cmap;
  GC draw_gc, erase_gc;
  unsigned int fg, bg;
  int x, y, size;
  XWindowAttributes xgwa;
  XGetWindowAttributes (dpy, window, &xgwa);
  cmap = xgwa.colormap;
  if (xgwa.width > xgwa.height) size = xgwa.height;
  else size = xgwa.width;
  if (size > 40) size -= 30;
  x = (xgwa.width - size) / 2;
  y = (xgwa.height - size) / 2;
  XtSetArg (av [ac], XtNforeground, &fg); ac++;
  XtSetArg (av [ac], XtNbackground, &bg); ac++;
  XtGetValues (button, av, ac);
  /* if it's black on white, swap it cause it looks better (hack hack) */
  if (fg == BlackPixelOfScreen (screen) && bg == WhitePixelOfScreen (screen))
    fg = WhitePixelOfScreen (screen), bg = BlackPixelOfScreen (screen);
  gcv.foreground = bg;
  erase_gc = XCreateGC (dpy, window, GCForeground, &gcv);
  gcv.foreground = fg;
  draw_gc = XCreateGC (dpy, window, GCForeground, &gcv);
  XFillRectangle (dpy, window, erase_gc, 0, 0, xgwa.width, xgwa.height);
  skull (dpy, window, draw_gc, erase_gc, x, y, size, size);
  XFreeGC (dpy, draw_gc);
  XFreeGC (dpy, erase_gc);
}

static void
#ifdef __STDC__
make_passwd_dialog (Widget parent)
#else /* ! __STDC__ */
make_passwd_dialog (parent) Widget parent;
#endif /* ! __STDC__ */
{
  char *username = 0;

#ifdef NO_MOTIF
  Widget box, passwd_label2;

  passwd_dialog = 
    XtVaCreatePopupShell("passwd_dialog", transientShellWidgetClass, parent,
			 XtNtitle, NULL,
			 XtNoverrideRedirect, TRUE,
			 NULL);

  box = XtVaCreateManagedWidget("box", formWidgetClass, passwd_dialog,
			    XtNleft, XtChainLeft,
			    XtNright, XtChainRight,
			    XtNtop, XtChainTop,
			    XtNbottom, XtChainBottom,
			    NULL);

  roger_label = XtVaCreateManagedWidget("roger", labelWidgetClass, box,
					XtNlabel, "",
					XtNleft, XtChainLeft,
					XtNright, XtChainRight,
					XtNtop, XtChainTop,
					NULL);

  passwd_label1 = XtVaCreateManagedWidget("label1", labelWidgetClass, box,
					  XtNfromHoriz, roger_label,
					  XtNright, XtChainRight,
					  XtNtop, XtChainTop,
					  NULL);
  passwd_label2 = XtVaCreateManagedWidget("label2", labelWidgetClass, box,
					  XtNfromHoriz, roger_label,
					  XtNright, XtChainRight,
					  XtNfromVert, passwd_label1,
					  NULL);
  passwd_label3 = XtVaCreateManagedWidget("label3", labelWidgetClass, box,
					  XtNfromHoriz, roger_label,
					  XtNright, XtChainRight,
					  XtNfromVert, passwd_label2,
					  NULL);
  
  passwd_form =
    XtVaCreateManagedWidget("passwd_form", dialogWidgetClass, box,
			    XtNvalue, typed_passwd,
			    XtNfromHoriz, roger_label,
			    XtNright, XtChainRight,
			    XtNfromVert, passwd_label3,
			    NULL);

  XawDialogAddButton(passwd_form,"ok", passwd_done_cb, 0);
  XawDialogAddButton(passwd_form,"cancel", passwd_cancel_cb, 0);
  passwd_done = XtNameToWidget(passwd_form,"ok");
  passwd_text = XtNameToWidget(passwd_form,"value");

  XtAppAddActions(XtWidgetToApplicationContext(passwd_text), 
		  actionsList, XtNumber(actionsList));
  XtOverrideTranslations(passwd_text, XtParseTranslationTable(Translations));

#else  /* Motif */

  create_passwd_dialog (parent);

  XtAddCallback (passwd_done, XmNactivateCallback, passwd_done_cb, 0);
  XtAddCallback (passwd_cancel, XmNactivateCallback, passwd_cancel_cb, 0);
  XtAddCallback (roger_label, XmNexposeCallback, roger, 0);

# ifdef VERIFY_CALLBACK_WORKS
  XtAddCallback (passwd_text, XmNmodifyVerifyCallback, check_passwd_cb, 0);
  XtAddCallback (passwd_text, XmNactivateCallback, check_passwd_cb, 0);
# else
  XtAddCallback (passwd_text, XmNactivateCallback, passwd_done_cb, 0);
  XtOverrideTranslations (passwd_text, XtParseTranslationTable (translations));
# endif

# if !defined(NO_MOTIF) && (XmVersion >= 1002)
  /* The focus stuff changed around; this didn't exist in 1.1.5. */
  XtVaSetValues (passwd_form, XmNinitialFocus, passwd_text, 0);
# endif

  /* Another random thing necessary in 1.2.1 but not 1.1.5... */
  XtVaSetValues (roger_label, XmNborderWidth, 2, 0);

#endif /* Motif */

#ifndef VMS
  {
    struct passwd *pw = getpwuid (getuid ());
    username = pw->pw_name;
  }
#else  /* VMS -- from "R.S.Niranjan" <U00C782%BRKVC1@navistar.com> who says
	         that on OpenVMS 6.1, using `struct passwd' crashes... */
  username = getenv("USER");
#endif /* VMS */

  format_into_label (passwd_label1, screensaver_version);
  format_into_label (passwd_label3, (username ? username : "???"));
}

extern void idle_timer P((void *, XtPointer));

static int passwd_idle_timer_tick;
static XtIntervalId id;

static void
#ifdef __STDC__
passwd_idle_timer (void *junk1, XtPointer junk2)
#else /* ! __STDC__ */
passwd_idle_timer (junk1, junk2)
     void *junk1;
     XtPointer junk2;
#endif /* ! __STDC__ */
{
  Display *dpy = XtDisplay (passwd_form);
#ifdef NO_MOTIF
  Window window = XtWindow (passwd_form);
#else  /* MOTIF */
  Window window = XtWindow (XtParent(passwd_done));
#endif /* MOTIF */
  static Dimension x, y, d, s, ss;
  static GC gc = 0;
  int max = passwd_timeout / 1000;

  idle_timer (junk1, junk2);

  if (passwd_idle_timer_tick == max)  /* first time */
    {
      XGCValues gcv;
#ifndef NO_MOTIF
      unsigned long fg, bg, ts, bs;
      Dimension w = 0, h = 0;
      XtVaGetValues(XtParent(passwd_done),
		    XmNwidth, &w,
		    0);
      XtVaGetValues(passwd_done,
		    XmNheight, &h,
		    XmNy, &y,
		    XtNforeground, &fg,
		    XtNbackground, &bg,
		    XmNtopShadowColor, &ts,
		    XmNbottomShadowColor, &bs,
		    0);

      if (ts != bg && ts != fg)
	fg = ts;
      if (bs != bg && bs != fg)
	fg = bs;

      d = h / 2;
      if (d & 1) d++;

      x = (w / 2);

      x -= d/2;
      y += d/2;

#else  /* NO_MOTIF */

      Arg av [100];
      int ac = 0;
      unsigned long fg, bg;
      XtSetArg (av [ac], XtNheight, &d); ac++;
      XtGetValues (passwd_done, av, ac);
      ac = 0;
      XtSetArg (av [ac], XtNwidth, &x); ac++;
      XtSetArg (av [ac], XtNheight, &y); ac++;
      XtSetArg (av [ac], XtNforeground, &fg); ac++;
      XtSetArg (av [ac], XtNbackground, &bg); ac++;
      XtGetValues (passwd_form, av, ac);
      x -= d;
      y -= d;
      d -= 4;

#endif /* NO_MOTIF */

      gcv.foreground = fg;
      if (gc) XFreeGC (dpy, gc);
      gc = XCreateGC (dpy, window, GCForeground, &gcv);
      s = 360*64 / (passwd_idle_timer_tick - 1);
      ss = 90*64;
      XFillArc (dpy, window, gc, x, y, d, d, 0, 360*64);
      XSetForeground (dpy, gc, bg);
      x += 1;
      y += 1;
      d -= 2;
    }

  if (--passwd_idle_timer_tick)
    {
      id = XtAppAddTimeOut (app, 1000,
			    (XtTimerCallbackProc) passwd_idle_timer, 0);
      XFillArc (dpy, window, gc, x, y, d, d, ss, s);
      ss += s;
    }
}

extern void pop_up_dialog_box P((Widget, Widget, int));
extern int BadWindow_ehandler P((Display *, XErrorEvent *));

#ifdef NO_MOTIF
/* mostly copied from demo.c */
static void
#ifdef __STDC__
focus_fuckus (Widget dialog)
#else /* !__STDC__ */
focus_fuckus (dialog)
     Widget dialog;
#endif /* !__STDC__ */
{
  XSetInputFocus (XtDisplay (dialog), XtWindow (dialog),
		  RevertToParent, CurrentTime);
}

void
#ifdef __STDC__
pop_up_athena_dialog_box (Widget parent, Widget focus, Widget dialog,
			  Widget form, int where)
#else  /* !__STDC__ */
pop_up_athena_dialog_box (parent, focus, dialog, form, where)
     Widget parent, focus, dialog, form;
     int where;
#endif /* !__STDC__ */
{
  /* modified from demo.c */
  /* I'm sure this is the wrong way to pop up a dialog box, but I can't
     figure out how else to do it.

     It's important that the screensaver dialogs not get decorated or
     otherwise reparented by the window manager, because they need to be
     children of the *real* root window, not the WM's virtual root, in
     order for us to guarentee that they are visible above the screensaver
     window itself.
   */
  Arg av [100];
  int ac = 0;
  Dimension sw, sh, x, y, w, h;

  XtRealizeWidget(dialog);
  sw = WidthOfScreen (XtScreen (dialog));
  sh = HeightOfScreen (XtScreen (dialog));
  ac = 0;
  XtSetArg (av [ac], XtNwidth, &w); ac++;
  XtSetArg (av [ac], XtNheight, &h); ac++;
  XtGetValues (form, av, ac);
  switch (where)
    {
    case 0:	/* center it in the top-right quadrant */
      x = (sw/2 + w) / 2 + (sw/2) - w;
      y = (sh/2 + h) / 2 - h;
      break;
    case 1:	/* center it in the bottom-right quadrant */
      x = (sw/2 + w) / 2 + (sw/2) - w;
      y = (sh/2 + h) / 2 + (sh/2) - h;
      break;
    case 2:	/* center it on the screen */
      x = (sw + w) / 2 - w;
      y = (sh + h) / 2 - h;
      break;
    default:
      abort ();
    }
  if (x + w > sw) x = sw - w;
  if (y + h > sh) y = sh - h;
  ac = 0;
  XtVaSetValues(dialog,
		XtNx, x,
		XtNy, y,
		NULL);
  XtVaSetValues(form,
		XtNx, x,
		XtNy, y,
		NULL);
  XtPopup(dialog,XtGrabNone);
  focus_fuckus(focus);
}

static void
#ifdef __STDC__
passwd_set_label (char *buf, int len)
#else /* ! __STDC__ */
passwd_set_label (buf,len) char *buf; int len;
#endif /* ! __STDC__ */
{
  Widget label;
  if (!passwd_text)
    return;
  label=XtNameToWidget(XtParent(passwd_text),"*label");
  XtVaSetValues(label,
		XtNlabel, buf,
		NULL);
}
#endif /* NO_MOTIF */

static Bool
#ifdef __STDC__
pop_passwd_dialog (Widget parent)
#else /* ! __STDC__ */
pop_passwd_dialog (parent) Widget parent;
#endif /* ! __STDC__ */
{
  Display *dpy = XtDisplay (passwd_dialog);
  Window focus;
  int revert_to;
  typed_passwd [0] = 0;
  passwd_state = pw_read;
  text_field_set_string (passwd_text, "", 0);

  XGetInputFocus (dpy, &focus, &revert_to);
#if !defined(NO_MOTIF) && !defined(DESTROY_WORKS)
  /* This fucker blows up if we destroy the widget.  I can't figure
     out why.  The second destroy phase dereferences freed memory...
     So we just keep it around; but unrealizing or unmanaging it
     doesn't work right either, so we hack the window directly. FMH.
   */
  if (XtWindow (passwd_form))
    XMapRaised (dpy, XtWindow (passwd_dialog));
#endif

#ifdef NO_MOTIF
  pop_up_athena_dialog_box (parent, passwd_text, passwd_dialog,
			    passwd_form, 2);
#else
  pop_up_dialog_box (passwd_dialog, passwd_form, 2);
  XtManageChild (passwd_form);
#endif

#if !defined(NO_MOTIF) && (XmVersion < 1002)
  /* The focus stuff changed around; this causes problems in 1.2.1
     but is necessary in 1.1.5. */
  XmProcessTraversal (passwd_text, XmTRAVERSE_CURRENT);
#endif

  passwd_idle_timer_tick = passwd_timeout / 1000;
  id = XtAppAddTimeOut (app, 1000, (XtTimerCallbackProc) passwd_idle_timer, 0);

#ifdef NO_MOTIF
  if (roger_label)
    roger(roger_label, 0, 0);
#endif /* NO_MOTIF */

  XGrabServer (dpy);				/* ############ DANGER! */

  /* this call to ungrab used to be in main_loop() - see comment in
      xscreensaver.c around line 696. */
  ungrab_keyboard_and_mouse ();

  while (passwd_state == pw_read)
    {
      XEvent event;
      XtAppNextEvent (app, &event);
      /* wait for timer event */
      if (event.xany.type == 0 && passwd_idle_timer_tick == 0)
	passwd_state = pw_time;
      XtDispatchEvent (&event);
    }
  XUngrabServer (dpy);
  XSync (dpy, False);				/* ###### (danger over) */

  if (passwd_state != pw_time)
    XtRemoveTimeOut (id);

  if (passwd_state != pw_ok)
    {
      char *lose;
      switch (passwd_state)
	{
	case pw_time: lose = "Timed out!"; break;
	case pw_fail: lose = "Sorry!"; break;
	case pw_cancel: lose = 0; break;
	default: abort ();
	}
#ifndef NO_MOTIF
      XmProcessTraversal (passwd_cancel, 0); /* turn off I-beam */
#endif
      if (lose)
	{
#ifdef NO_MOTIF
	  /* show the message */
	  passwd_set_label(lose,strlen(lose)+1);

	  /* and clear the password line */
	  memset(typed_passwd, 0, PASSWDLEN);
	  text_field_set_string (passwd_text, "", 0);
#else
	  text_field_set_string (passwd_text, lose, strlen (lose) + 1);
#endif
	  passwd_idle_timer_tick = 1;
	  id = XtAppAddTimeOut (app, 3000,
				(XtTimerCallbackProc) passwd_idle_timer, 0);
	  while (1)
	    {
	      XEvent event;
	      XtAppNextEvent (app, &event);
	      if (event.xany.type == 0 &&	/* wait for timer event */
		  passwd_idle_timer_tick == 0)
		break;
	      XtDispatchEvent (&event);
	    }
	}
    }
  memset (typed_passwd, 0, sizeof (typed_passwd));
  text_field_set_string (passwd_text, "", 0);
  XtSetKeyboardFocus (parent, None);

#ifdef DESTROY_WORKS
  XtDestroyWidget (passwd_dialog);
  passwd_dialog = 0;
#else
  XUnmapWindow (XtDisplay (passwd_dialog), XtWindow (passwd_dialog));
#endif
  {
    XErrorHandler old_handler = XSetErrorHandler (BadWindow_ehandler);
    /* I don't understand why this doesn't refocus on the old selected
       window when MWM is running in click-to-type mode.  The value of
       `focus' seems to be correct. */
    XSetInputFocus (dpy, focus, revert_to, CurrentTime);
    XSync (dpy, False);
    XSetErrorHandler (old_handler);
  }

  return (passwd_state == pw_ok ? True : False);
}

Bool
#ifdef __STDC__
unlock_p (Widget parent)
#else /* ! __STDC__ */
unlock_p (parent) Widget parent;
#endif /* ! __STDC__ */
{
  static Bool initted = False;
  if (! initted)
    {
#ifndef VERIFY_CALLBACK_WORKS
      XtAppAddActions (app, actions, XtNumber (actions));
#endif
      passwd_dialog = 0;
      initted = True;
    }
  if (! passwd_dialog)
    make_passwd_dialog (parent);
  return pop_passwd_dialog (parent);
}

#endif /* !NO_LOCKING */
