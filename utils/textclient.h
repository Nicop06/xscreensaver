/* xscreensaver, Copyright (c) 2012 Jamie Zawinski <jwz@jwz.org>
 *
 * Permission to use, copy, modify, distribute, and sell this software and its
 * documentation for any purpose is hereby granted without fee, provided that
 * the above copyright notice appear in all copies and that both that
 * copyright notice and this permission notice appear in supporting
 * documentation.  No representations are made about the suitability of this
 * software for any purpose.  It is provided "as is" without express or 
 * implied warranty.
 *
 * Running "xscreensaver-text" and returning bytes from it.
 */

#ifndef __TEXTCLIENT_H__
#define __TEXTCLIENT_H__

# ifdef USE_IPHONE
#  undef HAVE_FORKPTY
# endif

typedef struct text_data text_data;

extern text_data *textclient_open (Display *);
extern void textclient_close (text_data *);
extern void textclient_reshape (text_data *,
                                int pix_w, int pix_h,
                                int char_w, int char_h);
extern int textclient_getc (text_data *);
extern Bool textclient_putc (text_data *, XKeyEvent *);

#endif /* __TEXTCLIENT_H__ */
