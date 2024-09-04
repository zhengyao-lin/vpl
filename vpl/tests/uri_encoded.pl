:- use_module(library(uri)).

go :- uri_encoded(path, '*.doubleclick-cn.net', '*.doubleclick-cn.net'),
      uri_encoded(path, '%sada', '%25sada').
