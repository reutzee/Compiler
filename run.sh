make -f ./Makefile sc/goo; set o1='scheme -q < goo.scm'; set o2='./goo'; echo "(equal? '($o1) '($o2))"> test.scm; scheme -q < test.scm