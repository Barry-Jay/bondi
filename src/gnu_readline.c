/* compile this with -DHAVE_GNU_READLINE if you want to use gnu's readline function */
/* gnu_readline.c
   to build:
        gcc -I /usr/local/lib/ocaml -I /usr/local/include -c gnu_readline.c
   (edit the paths according to your local setup)
*/

#include <stdio.h>
#include <string.h>
#include <caml/mlvalues.h>
#include <caml/alloc.h>
int inited = 0;

#if defined(HAVE_GNU_READLINE)
#include <readline/readline.h>
extern value caml_readline(value prompt) { 
  char *s;
  char *d;
  int n;
  value v;

  if (!inited) {
    rl_readline_name = "fish";
    rl_initialize();
    rl_bind_key(9,rl_insert); /* turn off tab completion */
    inited=1;
  }
  s = readline(String_val(prompt));
  if(s) {
    add_history(s);
    n = strlen(s);
    d = malloc(n+2);
    memcpy(d,s,n);
    free(s);
    d[n]='\n';
    d[n+1]='\0';
    v = copy_string(d);
    free(d);
  } else {
    v = copy_string("");
  }
  return v;
}

#else

static char buffer[8000];

extern value caml_readline(value prompt) { 
  char *s;
  value v;

  printf("%s",String_val(prompt));
  fflush(stdout);
  s = fgets(buffer, 8000, stdin); /* includes end of line */
  v = copy_string(s?s:"");
  return v;
}
#endif

extern value caml_isatty(value fd) {
  return Val_bool(isatty(Int_val(fd)));
}

/* end of file gnu_readline.c */
