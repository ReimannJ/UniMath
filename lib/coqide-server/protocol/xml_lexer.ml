# 1 "ide/coqide/protocol/xml_lexer.mll"
 (*
 * Xml Light, an small Xml parser/printer with DTD support.
 * Copyright (C) 2003 Nicolas Cannasse (ncannasse@motion-twin.com)
 *
 * This library is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Lesser General Public
 * License as published by the Free Software Foundation; either
 * version 2.1 of the License, or (at your option) any later version.
 *
 * This library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with this library; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
 *)

open Lexing

type error =
        | EUnterminatedComment
        | EUnterminatedString
        | EIdentExpected
        | ECloseExpected
        | ENodeExpected
        | EAttributeNameExpected
        | EAttributeValueExpected
        | EUnterminatedEntity

exception Error of error

type pos = int * int * int * int

type token =
        | Tag of string * (string * string) list * bool
        | PCData of string
        | Endtag of string
        | Eof

let last_pos = ref 0
and current_line = ref 0
and current_line_start = ref 0

let tmp = Buffer.create 200

let idents = Hashtbl.create 0

let _ = begin
        Hashtbl.add idents "nbsp;" " ";
        Hashtbl.add idents "gt;" ">";
        Hashtbl.add idents "lt;" "<";
        Hashtbl.add idents "amp;" "&";
        Hashtbl.add idents "apos;" "'";
        Hashtbl.add idents "quot;" "\"";
end

let init lexbuf =
        current_line := 1;
        current_line_start := lexeme_start lexbuf;
        last_pos := !current_line_start

let close lexbuf =
        Buffer.reset tmp

let pos lexbuf =
        !current_line , !current_line_start ,
        !last_pos ,
        lexeme_start lexbuf

let restore (cl,cls,lp,_) =
        current_line := cl;
        current_line_start := cls;
        last_pos := lp

let newline lexbuf =
        incr current_line;
        last_pos := lexeme_end lexbuf;
        current_line_start := !last_pos

let error lexbuf e =
        last_pos := lexeme_start lexbuf;
        raise (Error e)


# 89 "ide/coqide/protocol/xml_lexer.ml"
let __ocaml_lex_tables = {
  Lexing.lex_base =
   "\000\000\245\255\246\255\001\000\000\000\008\000\254\255\255\255\
    \000\000\010\000\252\255\000\000\001\000\253\255\249\255\011\000\
    \016\000\254\255\255\255\002\000\251\255\252\255\004\000\254\255\
    \255\255\002\000\253\255\013\000\251\255\252\255\003\000\254\255\
    \255\255\253\255\018\000\001\000\041\000\254\255\255\255\252\255\
    \039\000\254\255\103\000\255\255\233\000\042\001\254\255\120\001\
    \004\000\254\255\255\255\005\000\006\000\255\255\254\255\185\001\
    \254\255\007\002\021\000\253\255\049\000\041\000\060\000\217\000\
    \254\255\255\255\065\002\251\255\252\255\253\255\003\000\255\255\
    \254\255\062\002\251\255\252\255\253\255\005\000\255\255\254\255\
    ";
  Lexing.lex_backtrk =
   "\255\255\255\255\255\255\008\000\007\000\005\000\255\255\255\255\
    \004\000\005\000\255\255\255\255\255\255\255\255\255\255\003\000\
    \002\000\255\255\255\255\255\255\255\255\255\255\004\000\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\004\000\255\255\
    \255\255\255\255\005\000\004\000\002\000\255\255\255\255\255\255\
    \255\255\255\255\001\000\255\255\255\255\255\255\255\255\000\000\
    \255\255\255\255\255\255\002\000\255\255\255\255\255\255\255\255\
    \255\255\000\000\255\255\255\255\002\000\002\000\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\004\000\255\255\
    \255\255\255\255\255\255\255\255\255\255\004\000\255\255\255\255\
    ";
  Lexing.lex_default =
   "\003\000\000\000\000\000\003\000\255\255\255\255\000\000\000\000\
    \255\255\255\255\000\000\255\255\255\255\000\000\000\000\255\255\
    \255\255\000\000\000\000\020\000\000\000\000\000\255\255\000\000\
    \000\000\255\255\000\000\028\000\000\000\000\000\255\255\000\000\
    \000\000\000\000\036\000\255\255\036\000\000\000\000\000\000\000\
    \041\000\000\000\255\255\000\000\255\255\046\000\000\000\255\255\
    \049\000\000\000\000\000\255\255\255\255\000\000\000\000\056\000\
    \000\000\255\255\059\000\000\000\255\255\255\255\255\255\255\255\
    \000\000\000\000\067\000\000\000\000\000\000\000\255\255\000\000\
    \000\000\074\000\000\000\000\000\000\000\255\255\000\000\000\000\
    ";
  Lexing.lex_trans =
   "\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\008\000\006\000\255\255\023\000\007\000\255\255\024\000\
    \000\000\009\000\000\000\009\000\016\000\017\000\000\000\031\000\
    \018\000\016\000\032\000\000\000\037\000\000\000\061\000\038\000\
    \008\000\000\000\000\000\014\000\039\000\072\000\004\000\255\255\
    \009\000\011\000\009\000\016\000\079\000\012\000\013\000\022\000\
    \016\000\025\000\063\000\255\255\052\000\061\000\255\255\008\000\
    \035\000\008\000\062\000\000\000\005\000\255\255\001\000\255\255\
    \026\000\033\000\050\000\053\000\054\000\062\000\000\000\010\000\
    \000\000\063\000\000\000\000\000\030\000\000\000\255\255\255\255\
    \255\255\062\000\060\000\065\000\000\000\000\000\000\000\000\000\
    \064\000\000\000\000\000\000\000\062\000\000\000\065\000\072\000\
    \000\000\079\000\000\000\064\000\000\000\255\255\062\000\255\255\
    \042\000\042\000\042\000\042\000\042\000\042\000\042\000\042\000\
    \042\000\042\000\042\000\042\000\042\000\042\000\042\000\042\000\
    \042\000\042\000\042\000\042\000\042\000\042\000\042\000\042\000\
    \042\000\042\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \042\000\042\000\042\000\042\000\042\000\042\000\042\000\042\000\
    \042\000\042\000\042\000\042\000\042\000\042\000\042\000\042\000\
    \042\000\042\000\042\000\042\000\042\000\042\000\042\000\042\000\
    \042\000\042\000\043\000\000\000\000\000\000\000\000\000\000\000\
    \044\000\044\000\044\000\044\000\044\000\044\000\044\000\044\000\
    \044\000\044\000\044\000\044\000\044\000\044\000\044\000\044\000\
    \044\000\044\000\044\000\044\000\044\000\044\000\044\000\044\000\
    \044\000\044\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \044\000\044\000\044\000\044\000\044\000\044\000\044\000\044\000\
    \044\000\044\000\044\000\044\000\044\000\044\000\044\000\044\000\
    \044\000\044\000\044\000\044\000\044\000\044\000\044\000\044\000\
    \044\000\044\000\063\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\063\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \002\000\255\255\021\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\029\000\000\000\000\000\
    \000\000\000\000\255\255\000\000\000\000\000\000\062\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\043\000\000\000\000\000\000\000\
    \000\000\255\255\044\000\044\000\044\000\044\000\044\000\044\000\
    \044\000\044\000\044\000\044\000\044\000\044\000\044\000\044\000\
    \044\000\044\000\044\000\044\000\044\000\044\000\044\000\044\000\
    \044\000\044\000\044\000\044\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\044\000\044\000\044\000\044\000\044\000\044\000\
    \044\000\044\000\044\000\044\000\044\000\044\000\044\000\044\000\
    \044\000\044\000\044\000\044\000\044\000\044\000\044\000\044\000\
    \044\000\044\000\044\000\044\000\047\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\047\000\047\000\047\000\047\000\047\000\
    \047\000\047\000\047\000\047\000\047\000\047\000\047\000\047\000\
    \047\000\047\000\047\000\047\000\047\000\047\000\047\000\047\000\
    \047\000\047\000\047\000\047\000\047\000\000\000\000\000\000\000\
    \000\000\047\000\000\000\047\000\047\000\047\000\047\000\047\000\
    \047\000\047\000\047\000\047\000\047\000\047\000\047\000\047\000\
    \047\000\047\000\047\000\047\000\047\000\047\000\047\000\047\000\
    \047\000\047\000\047\000\047\000\047\000\047\000\047\000\000\000\
    \047\000\047\000\047\000\047\000\047\000\047\000\047\000\047\000\
    \047\000\047\000\047\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\047\000\047\000\047\000\047\000\047\000\047\000\047\000\
    \047\000\047\000\047\000\047\000\047\000\047\000\047\000\047\000\
    \047\000\047\000\047\000\047\000\047\000\047\000\047\000\047\000\
    \047\000\047\000\047\000\000\000\000\000\000\000\000\000\047\000\
    \000\000\047\000\047\000\047\000\047\000\047\000\047\000\047\000\
    \047\000\047\000\047\000\047\000\047\000\047\000\047\000\047\000\
    \047\000\047\000\047\000\047\000\047\000\047\000\047\000\047\000\
    \047\000\047\000\047\000\057\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\057\000\057\000\057\000\057\000\057\000\057\000\
    \057\000\057\000\057\000\057\000\057\000\057\000\057\000\057\000\
    \057\000\057\000\057\000\057\000\057\000\057\000\057\000\057\000\
    \057\000\057\000\057\000\057\000\000\000\000\000\000\000\000\000\
    \057\000\000\000\057\000\057\000\057\000\057\000\057\000\057\000\
    \057\000\057\000\057\000\057\000\057\000\057\000\057\000\057\000\
    \057\000\057\000\057\000\057\000\057\000\057\000\057\000\057\000\
    \057\000\057\000\057\000\057\000\057\000\057\000\000\000\057\000\
    \057\000\057\000\057\000\057\000\057\000\057\000\057\000\057\000\
    \057\000\057\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \057\000\057\000\057\000\057\000\057\000\057\000\057\000\057\000\
    \057\000\057\000\057\000\057\000\057\000\057\000\057\000\057\000\
    \057\000\057\000\057\000\057\000\057\000\057\000\057\000\057\000\
    \057\000\057\000\000\000\071\000\076\000\078\000\057\000\069\000\
    \057\000\057\000\057\000\057\000\057\000\057\000\057\000\057\000\
    \057\000\057\000\057\000\057\000\057\000\057\000\057\000\057\000\
    \057\000\057\000\057\000\057\000\057\000\057\000\057\000\057\000\
    \057\000\057\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\077\000\000\000\000\000\070\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\075\000\000\000\
    \000\000\068\000";
  Lexing.lex_check =
   "\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\008\000\000\000\003\000\019\000\000\000\003\000\019\000\
    \255\255\005\000\255\255\009\000\015\000\015\000\255\255\027\000\
    \015\000\016\000\027\000\255\255\034\000\255\255\058\000\034\000\
    \008\000\255\255\255\255\004\000\035\000\070\000\000\000\003\000\
    \005\000\005\000\009\000\015\000\077\000\011\000\012\000\019\000\
    \016\000\022\000\061\000\036\000\051\000\058\000\036\000\005\000\
    \034\000\009\000\060\000\255\255\000\000\003\000\000\000\003\000\
    \025\000\030\000\048\000\051\000\052\000\062\000\255\255\005\000\
    \255\255\061\000\255\255\255\255\027\000\255\255\034\000\036\000\
    \034\000\060\000\058\000\060\000\255\255\255\255\255\255\255\255\
    \060\000\255\255\255\255\255\255\062\000\255\255\062\000\070\000\
    \255\255\077\000\255\255\062\000\255\255\036\000\061\000\036\000\
    \040\000\040\000\040\000\040\000\040\000\040\000\040\000\040\000\
    \040\000\040\000\040\000\040\000\040\000\040\000\040\000\040\000\
    \040\000\040\000\040\000\040\000\040\000\040\000\040\000\040\000\
    \040\000\040\000\255\255\255\255\255\255\255\255\255\255\255\255\
    \040\000\040\000\040\000\040\000\040\000\040\000\040\000\040\000\
    \040\000\040\000\040\000\040\000\040\000\040\000\040\000\040\000\
    \040\000\040\000\040\000\040\000\040\000\040\000\040\000\040\000\
    \040\000\040\000\042\000\255\255\255\255\255\255\255\255\255\255\
    \042\000\042\000\042\000\042\000\042\000\042\000\042\000\042\000\
    \042\000\042\000\042\000\042\000\042\000\042\000\042\000\042\000\
    \042\000\042\000\042\000\042\000\042\000\042\000\042\000\042\000\
    \042\000\042\000\255\255\255\255\255\255\255\255\255\255\255\255\
    \042\000\042\000\042\000\042\000\042\000\042\000\042\000\042\000\
    \042\000\042\000\042\000\042\000\042\000\042\000\042\000\042\000\
    \042\000\042\000\042\000\042\000\042\000\042\000\042\000\042\000\
    \042\000\042\000\063\000\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\063\000\255\255\255\255\255\255\255\255\255\255\255\255\
    \000\000\003\000\019\000\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\027\000\255\255\255\255\
    \255\255\255\255\034\000\255\255\255\255\255\255\063\000\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\044\000\255\255\255\255\255\255\
    \255\255\036\000\044\000\044\000\044\000\044\000\044\000\044\000\
    \044\000\044\000\044\000\044\000\044\000\044\000\044\000\044\000\
    \044\000\044\000\044\000\044\000\044\000\044\000\044\000\044\000\
    \044\000\044\000\044\000\044\000\255\255\255\255\255\255\255\255\
    \255\255\255\255\044\000\044\000\044\000\044\000\044\000\044\000\
    \044\000\044\000\044\000\044\000\044\000\044\000\044\000\044\000\
    \044\000\044\000\044\000\044\000\044\000\044\000\044\000\044\000\
    \044\000\044\000\044\000\044\000\045\000\255\255\255\255\255\255\
    \255\255\255\255\255\255\045\000\045\000\045\000\045\000\045\000\
    \045\000\045\000\045\000\045\000\045\000\045\000\045\000\045\000\
    \045\000\045\000\045\000\045\000\045\000\045\000\045\000\045\000\
    \045\000\045\000\045\000\045\000\045\000\255\255\255\255\255\255\
    \255\255\045\000\255\255\045\000\045\000\045\000\045\000\045\000\
    \045\000\045\000\045\000\045\000\045\000\045\000\045\000\045\000\
    \045\000\045\000\045\000\045\000\045\000\045\000\045\000\045\000\
    \045\000\045\000\045\000\045\000\045\000\047\000\047\000\255\255\
    \047\000\047\000\047\000\047\000\047\000\047\000\047\000\047\000\
    \047\000\047\000\047\000\255\255\255\255\255\255\255\255\255\255\
    \255\255\047\000\047\000\047\000\047\000\047\000\047\000\047\000\
    \047\000\047\000\047\000\047\000\047\000\047\000\047\000\047\000\
    \047\000\047\000\047\000\047\000\047\000\047\000\047\000\047\000\
    \047\000\047\000\047\000\255\255\255\255\255\255\255\255\047\000\
    \255\255\047\000\047\000\047\000\047\000\047\000\047\000\047\000\
    \047\000\047\000\047\000\047\000\047\000\047\000\047\000\047\000\
    \047\000\047\000\047\000\047\000\047\000\047\000\047\000\047\000\
    \047\000\047\000\047\000\055\000\255\255\255\255\255\255\255\255\
    \255\255\255\255\055\000\055\000\055\000\055\000\055\000\055\000\
    \055\000\055\000\055\000\055\000\055\000\055\000\055\000\055\000\
    \055\000\055\000\055\000\055\000\055\000\055\000\055\000\055\000\
    \055\000\055\000\055\000\055\000\255\255\255\255\255\255\255\255\
    \055\000\255\255\055\000\055\000\055\000\055\000\055\000\055\000\
    \055\000\055\000\055\000\055\000\055\000\055\000\055\000\055\000\
    \055\000\055\000\055\000\055\000\055\000\055\000\055\000\055\000\
    \055\000\055\000\055\000\055\000\057\000\057\000\255\255\057\000\
    \057\000\057\000\057\000\057\000\057\000\057\000\057\000\057\000\
    \057\000\057\000\255\255\255\255\255\255\255\255\255\255\255\255\
    \057\000\057\000\057\000\057\000\057\000\057\000\057\000\057\000\
    \057\000\057\000\057\000\057\000\057\000\057\000\057\000\057\000\
    \057\000\057\000\057\000\057\000\057\000\057\000\057\000\057\000\
    \057\000\057\000\255\255\066\000\073\000\073\000\057\000\066\000\
    \057\000\057\000\057\000\057\000\057\000\057\000\057\000\057\000\
    \057\000\057\000\057\000\057\000\057\000\057\000\057\000\057\000\
    \057\000\057\000\057\000\057\000\057\000\057\000\057\000\057\000\
    \057\000\057\000\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\073\000\255\255\255\255\066\000\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\073\000\255\255\
    \255\255\066\000";
  Lexing.lex_base_code =
   "";
  Lexing.lex_backtrk_code =
   "";
  Lexing.lex_default_code =
   "";
  Lexing.lex_trans_code =
   "";
  Lexing.lex_check_code =
   "";
  Lexing.lex_code =
   "";
}

let rec token lexbuf =
   __ocaml_lex_token_rec lexbuf 0
and __ocaml_lex_token_rec lexbuf __ocaml_lex_state =
  match Lexing.engine __ocaml_lex_tables __ocaml_lex_state lexbuf with
      | 0 ->
# 98 "ide/coqide/protocol/xml_lexer.mll"
                (
                        PCData "\r"
                )
# 362 "ide/coqide/protocol/xml_lexer.ml"

  | 1 ->
# 102 "ide/coqide/protocol/xml_lexer.mll"
                (
                        newline lexbuf;
                        PCData "\n"
                )
# 370 "ide/coqide/protocol/xml_lexer.ml"

  | 2 ->
# 107 "ide/coqide/protocol/xml_lexer.mll"
                (
                        last_pos := lexeme_start lexbuf;
                        comment lexbuf;
                        token lexbuf
                )
# 379 "ide/coqide/protocol/xml_lexer.ml"

  | 3 ->
# 113 "ide/coqide/protocol/xml_lexer.mll"
                (
                        last_pos := lexeme_start lexbuf;
                        header lexbuf;
                        token lexbuf;
                )
# 388 "ide/coqide/protocol/xml_lexer.ml"

  | 4 ->
# 119 "ide/coqide/protocol/xml_lexer.mll"
                (
                        last_pos := lexeme_start lexbuf;
                        let tag = ident_name lexbuf in
                        ignore_spaces lexbuf;
                        close_tag lexbuf;
                        Endtag tag
                )
# 399 "ide/coqide/protocol/xml_lexer.ml"

  | 5 ->
# 127 "ide/coqide/protocol/xml_lexer.mll"
                (
                        last_pos := lexeme_start lexbuf;
                        let tag = ident_name lexbuf in
                        ignore_spaces lexbuf;
                        let attribs, closed = attributes lexbuf in
                        Tag(tag, attribs, closed)
                )
# 410 "ide/coqide/protocol/xml_lexer.ml"

  | 6 ->
# 135 "ide/coqide/protocol/xml_lexer.mll"
                (
                        last_pos := lexeme_start lexbuf;
                        Buffer.reset tmp;
                        Buffer.add_string tmp (lexeme lexbuf);
                        PCData (pcdata lexbuf)
                )
# 420 "ide/coqide/protocol/xml_lexer.ml"

  | 7 ->
# 142 "ide/coqide/protocol/xml_lexer.mll"
                (
                        last_pos := lexeme_start lexbuf;
                        Buffer.reset tmp;
                        Buffer.add_string tmp (entity lexbuf);
                        PCData (pcdata lexbuf)
                )
# 430 "ide/coqide/protocol/xml_lexer.ml"

  | 8 ->
# 149 "ide/coqide/protocol/xml_lexer.mll"
                (
                        last_pos := lexeme_start lexbuf;
                        Buffer.reset tmp;
                        Buffer.add_string tmp (lexeme lexbuf);
                        PCData (pcdata lexbuf)
                )
# 440 "ide/coqide/protocol/xml_lexer.ml"

  | 9 ->
# 155 "ide/coqide/protocol/xml_lexer.mll"
              ( Eof )
# 445 "ide/coqide/protocol/xml_lexer.ml"

  | 10 ->
# 157 "ide/coqide/protocol/xml_lexer.mll"
                ( error lexbuf ENodeExpected )
# 450 "ide/coqide/protocol/xml_lexer.ml"

  | __ocaml_lex_state -> lexbuf.Lexing.refill_buff lexbuf;
      __ocaml_lex_token_rec lexbuf __ocaml_lex_state

and ignore_spaces lexbuf =
   __ocaml_lex_ignore_spaces_rec lexbuf 15
and __ocaml_lex_ignore_spaces_rec lexbuf __ocaml_lex_state =
  match Lexing.engine __ocaml_lex_tables __ocaml_lex_state lexbuf with
      | 0 ->
# 161 "ide/coqide/protocol/xml_lexer.mll"
                (
                        ignore_spaces lexbuf
                )
# 464 "ide/coqide/protocol/xml_lexer.ml"

  | 1 ->
# 165 "ide/coqide/protocol/xml_lexer.mll"
                (
                        newline lexbuf;
                        ignore_spaces lexbuf
                )
# 472 "ide/coqide/protocol/xml_lexer.ml"

  | 2 ->
# 170 "ide/coqide/protocol/xml_lexer.mll"
                ( ignore_spaces lexbuf )
# 477 "ide/coqide/protocol/xml_lexer.ml"

  | 3 ->
# 172 "ide/coqide/protocol/xml_lexer.mll"
                ( () )
# 482 "ide/coqide/protocol/xml_lexer.ml"

  | __ocaml_lex_state -> lexbuf.Lexing.refill_buff lexbuf;
      __ocaml_lex_ignore_spaces_rec lexbuf __ocaml_lex_state

and comment lexbuf =
   __ocaml_lex_comment_rec lexbuf 19
and __ocaml_lex_comment_rec lexbuf __ocaml_lex_state =
  match Lexing.engine __ocaml_lex_tables __ocaml_lex_state lexbuf with
      | 0 ->
# 176 "ide/coqide/protocol/xml_lexer.mll"
                (
                        comment lexbuf
                )
# 496 "ide/coqide/protocol/xml_lexer.ml"

  | 1 ->
# 180 "ide/coqide/protocol/xml_lexer.mll"
                (
                        newline lexbuf;
                        comment lexbuf
                )
# 504 "ide/coqide/protocol/xml_lexer.ml"

  | 2 ->
# 185 "ide/coqide/protocol/xml_lexer.mll"
                ( () )
# 509 "ide/coqide/protocol/xml_lexer.ml"

  | 3 ->
# 187 "ide/coqide/protocol/xml_lexer.mll"
                ( raise (Error EUnterminatedComment) )
# 514 "ide/coqide/protocol/xml_lexer.ml"

  | 4 ->
# 189 "ide/coqide/protocol/xml_lexer.mll"
                ( comment lexbuf )
# 519 "ide/coqide/protocol/xml_lexer.ml"

  | __ocaml_lex_state -> lexbuf.Lexing.refill_buff lexbuf;
      __ocaml_lex_comment_rec lexbuf __ocaml_lex_state

and header lexbuf =
   __ocaml_lex_header_rec lexbuf 27
and __ocaml_lex_header_rec lexbuf __ocaml_lex_state =
  match Lexing.engine __ocaml_lex_tables __ocaml_lex_state lexbuf with
      | 0 ->
# 193 "ide/coqide/protocol/xml_lexer.mll"
                (
                        header lexbuf
                )
# 533 "ide/coqide/protocol/xml_lexer.ml"

  | 1 ->
# 197 "ide/coqide/protocol/xml_lexer.mll"
                (
                        newline lexbuf;
                        header lexbuf
                )
# 541 "ide/coqide/protocol/xml_lexer.ml"

  | 2 ->
# 202 "ide/coqide/protocol/xml_lexer.mll"
                ( () )
# 546 "ide/coqide/protocol/xml_lexer.ml"

  | 3 ->
# 204 "ide/coqide/protocol/xml_lexer.mll"
                ( error lexbuf ECloseExpected )
# 551 "ide/coqide/protocol/xml_lexer.ml"

  | 4 ->
# 206 "ide/coqide/protocol/xml_lexer.mll"
                ( header lexbuf )
# 556 "ide/coqide/protocol/xml_lexer.ml"

  | __ocaml_lex_state -> lexbuf.Lexing.refill_buff lexbuf;
      __ocaml_lex_header_rec lexbuf __ocaml_lex_state

and pcdata lexbuf =
   __ocaml_lex_pcdata_rec lexbuf 34
and __ocaml_lex_pcdata_rec lexbuf __ocaml_lex_state =
  match Lexing.engine __ocaml_lex_tables __ocaml_lex_state lexbuf with
      | 0 ->
# 210 "ide/coqide/protocol/xml_lexer.mll"
                (
                        Buffer.add_char tmp '\r';
                        pcdata lexbuf
                )
# 571 "ide/coqide/protocol/xml_lexer.ml"

  | 1 ->
# 215 "ide/coqide/protocol/xml_lexer.mll"
                (
                        Buffer.add_char tmp '\n';
                        newline lexbuf;
                        pcdata lexbuf
                )
# 580 "ide/coqide/protocol/xml_lexer.ml"

  | 2 ->
# 221 "ide/coqide/protocol/xml_lexer.mll"
                (
                        Buffer.add_string tmp (lexeme lexbuf);
                        pcdata lexbuf
                )
# 588 "ide/coqide/protocol/xml_lexer.ml"

  | 3 ->
# 226 "ide/coqide/protocol/xml_lexer.mll"
                (
                        Buffer.add_string tmp (lexeme lexbuf);
                        pcdata lexbuf;
                )
# 596 "ide/coqide/protocol/xml_lexer.ml"

  | 4 ->
# 231 "ide/coqide/protocol/xml_lexer.mll"
                (
                        Buffer.add_string tmp (entity lexbuf);
                        pcdata lexbuf
                )
# 604 "ide/coqide/protocol/xml_lexer.ml"

  | 5 ->
# 236 "ide/coqide/protocol/xml_lexer.mll"
                ( Buffer.contents tmp )
# 609 "ide/coqide/protocol/xml_lexer.ml"

  | __ocaml_lex_state -> lexbuf.Lexing.refill_buff lexbuf;
      __ocaml_lex_pcdata_rec lexbuf __ocaml_lex_state

and entity lexbuf =
   __ocaml_lex_entity_rec lexbuf 40
and __ocaml_lex_entity_rec lexbuf __ocaml_lex_state =
  match Lexing.engine __ocaml_lex_tables __ocaml_lex_state lexbuf with
      | 0 ->
# 240 "ide/coqide/protocol/xml_lexer.mll"
                (
                        let ident = lexeme lexbuf in
                        try
                                Hashtbl.find idents (String.lowercase_ascii ident)
                        with
                                Not_found -> "&" ^ ident
                )
# 627 "ide/coqide/protocol/xml_lexer.ml"

  | 1 ->
# 248 "ide/coqide/protocol/xml_lexer.mll"
                ( raise (Error EUnterminatedEntity) )
# 632 "ide/coqide/protocol/xml_lexer.ml"

  | __ocaml_lex_state -> lexbuf.Lexing.refill_buff lexbuf;
      __ocaml_lex_entity_rec lexbuf __ocaml_lex_state

and ident_name lexbuf =
   __ocaml_lex_ident_name_rec lexbuf 45
and __ocaml_lex_ident_name_rec lexbuf __ocaml_lex_state =
  match Lexing.engine __ocaml_lex_tables __ocaml_lex_state lexbuf with
      | 0 ->
# 252 "ide/coqide/protocol/xml_lexer.mll"
                ( lexeme lexbuf )
# 644 "ide/coqide/protocol/xml_lexer.ml"

  | 1 ->
# 254 "ide/coqide/protocol/xml_lexer.mll"
                ( error lexbuf EIdentExpected )
# 649 "ide/coqide/protocol/xml_lexer.ml"

  | __ocaml_lex_state -> lexbuf.Lexing.refill_buff lexbuf;
      __ocaml_lex_ident_name_rec lexbuf __ocaml_lex_state

and close_tag lexbuf =
   __ocaml_lex_close_tag_rec lexbuf 48
and __ocaml_lex_close_tag_rec lexbuf __ocaml_lex_state =
  match Lexing.engine __ocaml_lex_tables __ocaml_lex_state lexbuf with
      | 0 ->
# 258 "ide/coqide/protocol/xml_lexer.mll"
                ( () )
# 661 "ide/coqide/protocol/xml_lexer.ml"

  | 1 ->
# 260 "ide/coqide/protocol/xml_lexer.mll"
                ( error lexbuf ECloseExpected )
# 666 "ide/coqide/protocol/xml_lexer.ml"

  | __ocaml_lex_state -> lexbuf.Lexing.refill_buff lexbuf;
      __ocaml_lex_close_tag_rec lexbuf __ocaml_lex_state

and attributes lexbuf =
   __ocaml_lex_attributes_rec lexbuf 51
and __ocaml_lex_attributes_rec lexbuf __ocaml_lex_state =
  match Lexing.engine __ocaml_lex_tables __ocaml_lex_state lexbuf with
      | 0 ->
# 264 "ide/coqide/protocol/xml_lexer.mll"
                ( [], false )
# 678 "ide/coqide/protocol/xml_lexer.ml"

  | 1 ->
# 266 "ide/coqide/protocol/xml_lexer.mll"
                ( [], true )
# 683 "ide/coqide/protocol/xml_lexer.ml"

  | 2 ->
# 268 "ide/coqide/protocol/xml_lexer.mll"
                (
                        let key = attribute lexbuf in
                        let data = attribute_data lexbuf in
                        ignore_spaces lexbuf;
                        let others, closed = attributes lexbuf in
                        (key, data) :: others, closed
                )
# 694 "ide/coqide/protocol/xml_lexer.ml"

  | __ocaml_lex_state -> lexbuf.Lexing.refill_buff lexbuf;
      __ocaml_lex_attributes_rec lexbuf __ocaml_lex_state

and attribute lexbuf =
   __ocaml_lex_attribute_rec lexbuf 55
and __ocaml_lex_attribute_rec lexbuf __ocaml_lex_state =
  match Lexing.engine __ocaml_lex_tables __ocaml_lex_state lexbuf with
      | 0 ->
# 278 "ide/coqide/protocol/xml_lexer.mll"
                ( lexeme lexbuf )
# 706 "ide/coqide/protocol/xml_lexer.ml"

  | 1 ->
# 280 "ide/coqide/protocol/xml_lexer.mll"
                ( error lexbuf EAttributeNameExpected )
# 711 "ide/coqide/protocol/xml_lexer.ml"

  | __ocaml_lex_state -> lexbuf.Lexing.refill_buff lexbuf;
      __ocaml_lex_attribute_rec lexbuf __ocaml_lex_state

and attribute_data lexbuf =
   __ocaml_lex_attribute_data_rec lexbuf 58
and __ocaml_lex_attribute_data_rec lexbuf __ocaml_lex_state =
  match Lexing.engine __ocaml_lex_tables __ocaml_lex_state lexbuf with
      | 0 ->
# 284 "ide/coqide/protocol/xml_lexer.mll"
                (
                        Buffer.reset tmp;
                        last_pos := lexeme_end lexbuf;
                        dq_string lexbuf
                )
# 727 "ide/coqide/protocol/xml_lexer.ml"

  | 1 ->
# 290 "ide/coqide/protocol/xml_lexer.mll"
                (
                        Buffer.reset tmp;
                        last_pos := lexeme_end lexbuf;
                        q_string lexbuf
                )
# 736 "ide/coqide/protocol/xml_lexer.ml"

  | 2 ->
# 296 "ide/coqide/protocol/xml_lexer.mll"
                ( error lexbuf EAttributeValueExpected )
# 741 "ide/coqide/protocol/xml_lexer.ml"

  | __ocaml_lex_state -> lexbuf.Lexing.refill_buff lexbuf;
      __ocaml_lex_attribute_data_rec lexbuf __ocaml_lex_state

and dq_string lexbuf =
   __ocaml_lex_dq_string_rec lexbuf 66
and __ocaml_lex_dq_string_rec lexbuf __ocaml_lex_state =
  match Lexing.engine __ocaml_lex_tables __ocaml_lex_state lexbuf with
      | 0 ->
# 300 "ide/coqide/protocol/xml_lexer.mll"
                ( Buffer.contents tmp )
# 753 "ide/coqide/protocol/xml_lexer.ml"

  | 1 ->
# 302 "ide/coqide/protocol/xml_lexer.mll"
                (
                        Buffer.add_char tmp (lexeme_char lexbuf 1);
                        dq_string lexbuf
                )
# 761 "ide/coqide/protocol/xml_lexer.ml"

  | 2 ->
# 307 "ide/coqide/protocol/xml_lexer.mll"
                (
                        Buffer.add_string tmp (entity lexbuf);
                        dq_string lexbuf
                )
# 769 "ide/coqide/protocol/xml_lexer.ml"

  | 3 ->
# 312 "ide/coqide/protocol/xml_lexer.mll"
                ( raise (Error EUnterminatedString) )
# 774 "ide/coqide/protocol/xml_lexer.ml"

  | 4 ->
# 314 "ide/coqide/protocol/xml_lexer.mll"
                (
                        Buffer.add_char tmp (lexeme_char lexbuf 0);
                        dq_string lexbuf
                )
# 782 "ide/coqide/protocol/xml_lexer.ml"

  | __ocaml_lex_state -> lexbuf.Lexing.refill_buff lexbuf;
      __ocaml_lex_dq_string_rec lexbuf __ocaml_lex_state

and q_string lexbuf =
   __ocaml_lex_q_string_rec lexbuf 73
and __ocaml_lex_q_string_rec lexbuf __ocaml_lex_state =
  match Lexing.engine __ocaml_lex_tables __ocaml_lex_state lexbuf with
      | 0 ->
# 321 "ide/coqide/protocol/xml_lexer.mll"
                ( Buffer.contents tmp )
# 794 "ide/coqide/protocol/xml_lexer.ml"

  | 1 ->
# 323 "ide/coqide/protocol/xml_lexer.mll"
                (
                        Buffer.add_char tmp (lexeme_char lexbuf 1);
                        q_string lexbuf
                )
# 802 "ide/coqide/protocol/xml_lexer.ml"

  | 2 ->
# 328 "ide/coqide/protocol/xml_lexer.mll"
                (
                        Buffer.add_string tmp (entity lexbuf);
                        q_string lexbuf
                )
# 810 "ide/coqide/protocol/xml_lexer.ml"

  | 3 ->
# 333 "ide/coqide/protocol/xml_lexer.mll"
                ( raise (Error EUnterminatedString) )
# 815 "ide/coqide/protocol/xml_lexer.ml"

  | 4 ->
# 335 "ide/coqide/protocol/xml_lexer.mll"
                (
                        Buffer.add_char tmp (lexeme_char lexbuf 0);
                        q_string lexbuf
                )
# 823 "ide/coqide/protocol/xml_lexer.ml"

  | __ocaml_lex_state -> lexbuf.Lexing.refill_buff lexbuf;
      __ocaml_lex_q_string_rec lexbuf __ocaml_lex_state

;;

