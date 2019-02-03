; $$$$$ FREE VARS $$$$$
%define FVAR(i) [fvar + i * WORD_SIZE]

; $$$$$ ATOMS $$$$$

; --- generic ---
%macro MAKE_LITERAL 2 ; Make a literal of type %1
                        ; followed by the definition %2
  db %1
  %2
%endmacro

; --- literal nil, void, bool, int, float, char ---
%define MAKE_NIL db T_NIL 
%define MAKE_VOID db T_VOID 
%define MAKE_BOOL(val) MAKE_LITERAL T_BOOL, db val
%define MAKE_LITERAL_INT(val) MAKE_LITERAL T_INTEGER, dq val
%define MAKE_LITERAL_FLOAT(val) MAKE_LITERAL T_INTEGER, dq val
%define MAKE_LITERAL_CHAR(val) MAKE_LITERAL T_CHAR ,db val

; --- literal string ---
%macro MAKE_LITERAL_STRING 1
  db T_STRING
  dq (%%end_str - %%str)
%%str:
  db %1
%%end_str:
%endmacro

; --- gettes atom data--- 
%define TYPE(r) byte [r] 
%define DATA(r) [r + TYPE_SIZE]
%define INT_DATA(r) qword DATA(r)
%define FLOAT_DATA(r) qword DATA(r)
%define CHAR_DATA(r) byte DATA(r)
%define BOOL_DATA(r) byte DATA(r)
%define STR_LEN(r) qword DATA(r)
%define STR_DATA_PTR(r) r + WORD_SIZE + TYPE_SIZE
%define STRING_REF(r,i) byte [r + WORD_SIZE + TYPE_SIZE + i]

; $$$$$ COMPLEX $$$$$

; --- literal pair ---
%macro MAKE_WORDS_LIT 3
  db %1
  dq %2
  dq %3
%endmacro

%define MAKE_LITERAL_PAIR(car,cdr) MAKE_WORDS_LIT T_PAIR, car, cdr

; --- literal vector ---
%macro MAKE_LITERAL_VECTOR 0-* 
  db T_VECTOR
  dq %0
%rep %0
    dq %1
%rotate 1
%endrep
%endmacro

; --- gettes complex data--- 
%define LOWER_DATA(sob) qword[sob+TYPE_SIZE]
%define UPPER_DATA(sob)qword[sob+WORD_BYTES+TYPE_SIZE]
%define CAR LOWER_DATA
%define CDR UPPER_DATA
%define VECTOR_LEN LOWER_DATA
%define VECTOR_REF(r,i) qword [r + TYPE_SIZE + WORD_SIZE + i * WORD_SIZE]