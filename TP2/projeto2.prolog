%--------------------------------- - - - - - - - - - -  -  -  -  -   -
% SIST. REPR. CONHECIMENTO E RACIOCINIO - MiEI/3

%--------------------------------- - - - - - - - - - -  -  -  -  -   -
% Base de Conhecimento com informacao genealogica.

%--------------------------------- - - - - - - - - - -  -  -  -  -   -
% SICStus PROLOG: Declaracoes iniciais

:- set_prolog_flag( discontiguous_warnings,off ).
:- set_prolog_flag( single_var_warnings,off ).
:- set_prolog_flag( unknown,fail ).

:- op(996, xfy, '&&' ).  % operador de conjuncao
:- op(997, xfy, '##' ).  % operador de disjuncao 

% Operador usado em invariantes avaliados apenas quando
% se evolui/involui conhecimento imperfeito impreciso
:- op(900,xfy,:~:).

% Operador usado em invariantes avaliados apenas quando
% se evolui/involui conhecimento imperfeito incerto/interdito
:- op(900,xfy,:-:).

:- op(900,xfy,:+:).

:- op(900,xfy,:*:).

% Definições iniciais
:- op(900,xfy,'::').
:- dynamic utente/4.
:- dynamic prestador/5.
:- dynamic cuidado/6.
:- dynamic perfeito/1.
:- dynamic excecao/1.
:- dynamic impreciso/1.
:- dynamic incerto/1.
:- dynamic incerto_morada/1.
:- dynamic incerto_idade/1.
:- dynamic incerto_especialidade/1.
:- dynamic incerto_instituicao/1.
:- dynamic incerto_cidade/1.
:- dynamic incerto_data/1.
:- dynamic incerto_utente/1.
:- dynamic incerto_prestador/1.
:- dynamic incerto_preco/1.
:- dynamic incerto_descricao/1.
:- dynamic nulo/1.
:- dynamic '-'/1.
:- dynamic '::'/2.

:- dynamic ':*:'/2.
:- dynamic ':+:'/2.

%--------------------------------- - - - - - - - - - -  -  -  -  -   -

% Extensao do meta-predicado nao: Questao -> {V,F}
nao( Questao ) :-
    Questao, !, fail.
nao( Questao ).


% Predicado que faz a disjuncao entre valores de verdade
disjuncao( verdadeiro, X, verdadeiro ).
disjuncao( X, verdadeiro, verdadeiro ).
disjuncao( desconhecido, Y, desconhecido ) :- Y \= verdadeiro.
disjuncao( Y, desconhecido, desconhecido ) :- Y \= verdadeiro.
disjuncao( falso, falso, falso ).

% Predicado que faz a conjuncao entre valores de verdade
conjuncao( verdadeiro, verdadeiro, verdadeiro ).
conjuncao( falso, _, falso ).
conjuncao( _, falso, falso ).
conjuncao( desconhecido, verdadeiro, desconhecido ).
conjuncao( verdadeiro, desconhecido, desconhecido ).


%--------------------------------- - - - - - - - - - -  -  -  -  -   -
% Extensao do meta-predicado si: Questao,Resposta -> {V,F}

si( P ## X, V ) :- 
  si( P, V1 ), 
  si( X, V2 ), 
  disjuncao( V1, V2, V ).
si( P && X, V ) :- 
  si( P, V1 ), 
  si( X, V2 ), 
  conjuncao( V1, V2, V ).
si( Questao,verdadeiro ) :-
    Questao.
si( Questao,falso ) :-
    -Questao.
si( Questao,desconhecido ) :-
    nao( Questao ),
    nao( -Questao ).


% Predicado comprimento:
% Lista, Comprimento -> {V,F}
comprimento([],0).
comprimento([H|T],N) :-
	comprimento(T,S),
	N is S+1. 

% Predicado solucoes:
% Termo, Predicado, Lista -> {V,F}
solucoes(T,Q,S) :- findall(T,Q,S).

%--------------------------------- - - - - - - - - - -  -  -  -  -   -
% 					FACTOS
%--------------------------------- - - - - - - - - - -  -  -  -  -   -

% utente: #IdUt, Nome, Sexo, Idade, Morada -> { V, F, D }
% Predicado que representa conhecimento relativo a utentes
-utente(Id,Nome,Idade,Morada) :-
  nao(utente(Id,Nome,Idade,Morada)),
  nao(excecao(utente(Id,Nome,Idade,Morada))).

%Conhecimento perfeito relativo a utentes na base de conhecimento

utente(1,joao_pimentel,20,esposende).
perfeito(utente(1)).

utente(2,bruno_veloso,22,ponte_da_barca).
perfeito(utente(2)).

utente(3,jaime_leite,20,felgueiras).
perfeito(utente(3)).

utente(4,pedro_goncalves,20,felgueiras).
perfeito(utente(4)).

utente(5,rodolfo_silva,20,trofa).
perfeito(utente(5)).

utente(6,joana_amorim,22,viana_do_castelo).
perfeito(utente(6)).

utente(7,gloria_borga,53,portimao).
perfeito(utente(7)).

utente(8,andreia_silva,27,trofa).
perfeito(utente(8)).

% prestador: #IdPrest, Nome, Especialidade, Instituição, Cidade ↝ { 𝕍, 𝔽, 𝔻 }
% Predicado que representa conhecimento relativo a prestadores
-prestador(Id,Nome,Especialidade,Instituicao,Cidade) :-
  nao(prestador(Id,Nome,Especialidade,Instituicao,Cidade)),
  nao(excecao(prestador(Id,Nome,Especialidade,Instituicao,Cidade))).

%Conhecimento perfeito relativo a prestadores na base de conhecimento

prestador(1,maria_antunes,medicina_geral,trofa_saude,braga).
perfeito(prestador(1)).

prestador(2,emanuel_orquidea,cardiologia,cuf,porto).
perfeito(prestador(2)).

prestador(3,orlando_beloom,oftalmologia,sao_joao,porto).
perfeito(prestador(3)).

prestador(4,jack_pardal,otorrinolarengologia,particular,viana).
perfeito(prestador(4)).

prestador(5,antonio_carlos,ginecologia,trofa_saude,braga).
perfeito(prestador(5)).

prestador(6,carlos_silva,cirurgia_geral,santo_antonio,porto).
perfeito(prestador(6)).

% cuidado: #IdCui, Data, #IdUt, #IdPrest, Descrição, Custo ↝ { 𝕍, 𝔽, 𝔻 }
% Predicado que representa conhecimento relativo a cuidados
-cuidado(Id,Data,Utente,Prestador,Descricao, Custo) :-
  nao(cuidado(Id,Data,Utente,Prestador,Descricao, Custo)),
  nao(excecao(cuidado(Id,Data,Utente,Prestador,Descricao, Custo))).

%Conhecimento perfeito relativo a cuidados na base de conhecimento

cuidado(1,06-03-2019,1,1,consulta_rotina,14).
perfeito(cuidado(1)).

cuidado(2,06-04-2014,1,3,visao_desfocada,22).
perfeito(cuidado(2)).

cuidado(3,07-03-2014,3,5,consulta_rotina,32).
perfeito(cuidado(3)).

cuidado(4,12-05-2019,5,2,prova_de_esforco,9).
perfeito(cuidado(4)).

cuidado(5,26-02-2019,2,5,consulta_rotina,10).
perfeito(cuidado(5)).

cuidado(6,29-12-2019,3,2,prova_de_esforco,15).
perfeito(cuidado(6)).

cuidado(7,07-03-2019, 1, 1,consulta_rotina,20).
perfeito(cuidado(7)).


% --------------------------------------------------------------------------
% Registar utentes, serviços e consultas;
adiciona(T) :- solucoes(Inv, +T::Inv, S),
               insere(T),
               testa(S).

% Predicado que representa a inserção de valores na base de conhecimento
insere(T) :- assert(T).
insere(T) :- retract(T),!,fail.

% Predicado de teste a valores relativos à base de conhecimento
testa([]).
testa([H|T]) :- H, testa(T).

%--------------------------------- - - - - - - - - - -  -  -  -  -   -
% ------------------------- INVARIANTES ---------------------------- %
%--------------------------------- - - - - - - - - - -  -  -  -  -   -

% Utente

% Invariantes que nao permitem inserir conhecimento perfeito
% se ja existir conhecimento perfeito

+utente(IdUt, Nome, Idade, Morada) :: (
  nao(perfeito(utente(IdUt)))
).

% Invariante que nao permite inserir conhecimento impreciso se
% ja existir conhecimento perfeito ou impreciso

+utente(IdUt, Nome, Idade, Morada) :~: (
  nao(perfeito(utente(IdUt))),
  nao(impreciso(utente(IdUt)))
).

% Invariante que nao permite a insercao de conhecimento
% incerto/interdito se ja existir conhecimento.
+utente(IdUt, Nome, Idade, Morada) :-: (
  nao(perfeito(utente(IdUt))),
  nao(impreciso(utente(IdUt))),
  nao(incerto(utente(IdUt)))
).

% Invariante que nao permite a insercao de conhecimento 
% negativo se ja existir conhecimento perfeito 
+(-utente(IdUt, Nome, Idade, Morada)) :: (
  nao(perfeito(utente(IdUt)))
).

% Invariante referencial: nao permitir que se remova um utente enquanto
%                         existirem cuidados associados a si
-utente(IdUt, _, _, _) :: (
  nao(cuidado(_, IdUt, _, _, _,_))
).

% Prestador


% PARTE II
% Invariante estrutural: nao permitir a insercao de conhecimento repetido

%+(-prestador(IdPro, Nome, Especialidade, Instituicao, Cidade)) :: (
%  solucoes(IdPro, -prestador(IdPro, Nome, Especialidade, Instituicao, Cidade), S),
%  comprimento(S, N),
%  N == 1
%).
+(-prestador(IdPro, Nome, Especialidade, Instituicao, Cidade)) :: (
  nao(perfeito(prestador(IdPro)))
).


% Invariantes que nao permitem inserir conhecimento perfeito
% se ja existir conhecimento perfeito

+prestador(IdUt, Nome, Especialidade, Instituicao, Cidade) :: (
  nao(perfeito(prestador(IdUt)))
).

% Invariante que nao permite inserir conhecimento impreciso se
% ja existir conhecimento perfeito ou impreciso

+prestador(IdUt, Nome, Especialidade, Instituicao, Cidade) :~: (
  nao(perfeito(prestador(IdUt))),
  nao(impreciso(prestador(IdUt)))
).

% Invariante que nao permite a insercao de conhecimento
% incerto/interdito se ja existir conhecimento.
+prestador(IdUt, Nome, Especialidade, Instituicao, Cidade) :-: (
  nao(perfeito(prestador(IdUt))),
  nao(impreciso(prestador(IdUt))),
  nao(incerto(prestador(IdUt)))
).

% Invariante referencial: nao permitir que se remova um utente enquanto
%                         existirem atos medicos associados a si
-prestador(IdUt, _, _, _,_) :: (
  nao(cuidado(_, _, IdUt, _, _,_))
).


% CUIDADOS !!!!!!!!!!!!!!!!!!!!!!!!!!

% Invariante referencial: nao permitir a insercao de atos medicos
%                         relativos a servicos ou utentes inexistentes

+cuidado(_,_, IdUt, IdPrest, _, _) :: (
  utente(IdUt, _, _, _),
  prestador(IdPrest, _, _, _,_)
).

+cuidado(_,_, IdUt, _, _, _) :+: (
  utente(IdUt, _, _, _)
).

+cuidado(_,_, _, IdPrest, _, _) :*: (
  prestador(IdPrest, _, _, _,_)
).

+cuidado(Id,Data,IdUt, IdPrest, Descricao, Custo) :: (
  nao(perfeito(cuidado(Id)))
).

% Invariante que nao permite inserir conhecimento impreciso se
% ja existir conhecimento perfeito ou impreciso

+cuidado(Id,Data,IdUt, IdPrest, Descricao, Custo) :~: (
  nao(perfeito(cuidado(Id))),
  nao(impreciso(cuidado(Id)))
).

% Invariante que nao permite a insercao de conhecimento
% incerto/interdito se ja existir conhecimento.
+cuidado(Id,Data,IdUt, IdPrest, Descricao, Custo) :-: (
  nao(perfeito(cuidado(Id))),
  nao(impreciso(cuidado(Id))),
  nao(incerto(cuidado(Id)))
).


%+(-cuidado(Id,Data,IdUt, IdPrest, Descricao, Custo)) :: (
%  solucoes(Id, -cuidado(Id,Data,IdUt, IdPrest, Descricao, Custo), S),
%  comprimento(S, N),
%  N == 1
%).
+(-cuidado(Id,Data,IdUt, IdPrest, Descricao, Custo)) :: (
  nao(perfeito(cuidado(Id)))
).














% ______________________________________________________________________________
% ______________________________________________________________________________
% ______________________________________________________________________________

% EVOLUCAO UTENTES 
% IMPERFEITO -> Morada ou Idade

%--------------------------------- - - - - - - - - - -  -  -  -  -   -
% Extensao do predicado evolucao_perfeito: evolucao_perfeito -> {V,F}

% Evolucao de conhecimento perfeito que remove conhecimento impreciso/incerto

% Predicado que acrescenta conhecimento perfeito relativo a um utente
evolucao_perfeito(utente(IdUt,Nome,Idade,Morada)) :-
  solucoes(Inv, +utente(IdUt,Nome,Idade,Morada)::Inv, LInv),
  testa(LInv),
  remover_impreciso(utente(IdUt,Nome,Idade,Morada)),
  assert(utente(IdUt,Nome,Idade,Morada)),
  assert(perfeito(utente(IdUt))).

% Predicado que acrescenta conhecimento perfeito relativo a um utente
evolucao_perfeito((-utente(IdUt, Nome, Idade, Morada))) :-
  solucoes(Inv, +(-utente(IdUt,Nome,Idade,Morada))::Inv, LInv),
  testa(LInv),
 % remover_impreciso(utente(IdUt,Nome,Idade,Morada)),
  assert((-utente(IdUt,Nome,Idade,Morada))),
  assert(perfeito(utente(IdUt))).


% Remocao de conhecimento impreciso (nao é involucao!)
% É procedimental, tal como os predicados de evolucao, solucoes, etc.

% Predicado que remove conhecimento impreciso relativamente a utentes
remover_impreciso(utente(IdUt, Nome, Idade, Morada)) :-
  retract(excecao(utente(IdUt,_,_,_))),
  remover_impreciso(utente(IdUt,Nome,Idade,Morada)).
remover_impreciso(utente(IdUt,Nome,Idade,Morada)) :-
  retract(impreciso(utente(IdUt))),
  remover_impreciso(utente(IdUT,Nome,Idade,Morada)).
remover_impreciso(utente(IdUt, Nome, Idade, Morada)) :-
  remover_incerto(utente(IdUt,Nome,Idade,Morada)).


% Remocao de conhecimento incerto (nao é involucao!!)

% Predicado que remove conhecimento incerto relativamente a utentes
remover_incerto(utente(IdUt,Nome,Idade,Morada)) :-
  incerto_idade(utente(IdUt,I)),
  retract((excecao(utente(Id,N,Ida,M)) :-
    utente(Id,N,I,M))),
  retract(utente(IdUt, _, _ ,_)),
  retract(incerto_idade(utente(IdUt, _))).
remover_incerto(utente(IdUt,Nome,Idade,Morada)) :-
  incerto_morada(utente(IdUt,I)),
  retract((excecao(utente(Id,N,Ida,M)) :-
    utente(Id,N,I,M))),
  retract(utente(IdUt, _, _ ,_)),
  retract(incerto_morada(utente(IdUt, _))).
remover_incerto(utente(IdUt,Nome,Idade,Morada)).


% Predicado que indica conhecimento incerto relativamente a utentes
incerto(utente(IdUt)) :-
  incerto_idade(utente(IdUt, _)).
incerto(utente(IdUt)) :-
  incerto_morada(utente(IdUt, _)).


% Evolucao de conhecimento impreciso que remove conhecimento incerto

%--------------------------------- - - - - - - - - - -  -  -  -  -   -
% Extensao do predicado evolucao_impreciso: EnumeracaoFactosAnomalos -> {V,F}

% Predicado que acrescenta conhecimento impreciso relativamente a utentes
evolucao_impreciso([utente(IdUt, Nome, Idade, Morada)|T]) :-
  T \= [],
  same_utente(T, IdUt),
  testaInvs([utente(IdUt, Nome, Idade, Morada)|T]),
  remover_incerto(utente(IdUt, Nome, Idade, Morada)),
  insere_excecoes([utente(IdUt, Nome, Idade, Morada)|T]).

% Predicado que verifica se dois utentes são iguais
same_utente([], _).
same_utente([utente(Id1, _, _, _) | T], Id2) :-
  Id1 == Id2,
  same_utente(T, Id2).

% Predicado de teste a invariantes
testaInvs([]).
testaInvs([P|Ps]) :-
  solucoes(Inv, +P::Inv, LInv1),
  solucoes(Inv, +P:~:Inv, LInv2),
  testa(LInv1),  
  testa(LInv2),
  testaInvs(Ps).

% Predicado que insere exceções relativas a utentes
insere_excecoes([]).
insere_excecoes([utente(IdUt, Nome, Idade, Morada)|Es]) :-
  assert(excecao(utente(IdUt, Nome, Idade, Morada))), 
  assert(impreciso(utente(IdUt))),
  insere_excecoes(Es).

% Predicado que acrescenta conhecimento incerto relativamente à idade de um utente
evolucao_incerto_idade(utente(IdUt, Nome, Idade, Morada)) :-
  solucoes(Inv, +utente(IdUt,Nome,Idade,Morada):-:Inv, LInv1),
  solucoes(Inv, +utente(IdUt, Nome, Idade, Morada)::Inv, LInv2),
  testa(LInv1),
  testa(LInv2),
  assert((excecao(utente(Id,N,I,M)) :-
         utente(Id,N,Idade,M))),
  assert(utente(IdUt, Nome, Idade, Morada)),
  assert(incerto_idade(utente(IdUt,Idade))).

% Predicado que acrescenta conhecimento interdito relativamente à idade de um utente
evolucao_interdito_idade(utente(IdUt, Nome, Idade, Morada)) :-
  solucoes(Inv, +utente(IdUt,Nome,Idade,Morada):-:Inv, LInv1),
  solucoes(Inv, +utente(IdUt, Nome, Idade, Morada)::Inv, LInv2),
  testa(LInv1),
  testa(LInv2),
  assert(nulo(Idade)),
  assert((excecao(utente(Id,N,I,M)) :-
         utente(Id,N,Idade,M))),
  assert((+utente(Id,N,I,M) :: (
               solucoes(Id,(utente(Id,_,Idade,_), nulo(Idade)),S),
               comprimento(S,0)
             ))),
  assert(utente(IdUt, Nome,Idade,Morada)).


% Predicado que acrescenta conhecimento incerto relativamente à morada de um utente
evolucao_incerto_morada(utente(IdUt, Nome, Idade, Morada)) :-
  solucoes(Inv, +utente(IdUt,Nome,Idade,Morada):-:Inv, LInv1),
  solucoes(Inv, +utente(IdUt, Nome, Idade, Morada)::Inv, LInv2),
  testa(LInv1),
  testa(LInv2),
  assert((excecao(utente(Id,N,I,M)) :-
         utente(Id,N,I,Morada))),
  assert(utente(IdUt, Nome, Idade, Morada)),
  assert(incerto_morada(utente(IdUt,Morada))).

% Predicado que acrescenta conhecimento interdito relativamente à morada de um utente
evolucao_interdito_morada(utente(IdUt, Nome, Idade, Morada)) :-
  solucoes(Inv, +utente(IdUt,Nome,Idade,Morada):-:Inv, LInv1),
  solucoes(Inv, +utente(IdUt, Nome, Idade, Morada)::Inv, LInv2),
  testa(LInv1),
  testa(LInv2),
  assert(nulo(Morada)),
  assert((excecao(utente(Id,N,I,M)) :-
         utente(Id,N,I,Morada))),
  assert((+utente(Id,N,I,M) :: (
               solucoes(Id,(utente(Id,_,_,Morada), nulo(Morada)),S),
               comprimento(S,0)
             ))),
  assert(utente(IdUt, Nome,Idade,Morada)).

% ______________________________________________________________________________
% ______________________________________________________________________________
% ______________________________________________________________________________

% EVOLUCAO PRESTADORES 
% IMPERFEITO -> Especialidade, instituicao ou Cidade

%--------------------------------- - - - - - - - - - -  -  -  -  -   -
% Extensao do predicado evolucao_perfeito: evolucao_perfeito -> {V,F}

% Evolucao de conhecimento perfeito que remove conhecimento impreciso/incerto

% Predicado que acrescenta conhecimento perfeito relativo a um prestador
evolucao_perfeito(prestador(IdUt,Nome,Especialidade,Instituicao,Cidade)) :-
  solucoes(Inv, +prestador(IdUt,Nome,Especialidade,Instituicao,Cidade)::Inv, LInv),
  testa(LInv),
  remover_impreciso(prestador(IdUt,Nome,Especialidade,Instituicao,Cidade)),
  assert(prestador(IdUt,Nome,Especialidade,Instituicao,Cidade)),
  assert(perfeito(prestador(IdUt))).

% Predicado que acrescenta conhecimento perfeito relativo a um prestador
evolucao_perfeito((-prestador(IdUt, Nome, Especialidade,Instituicao,Cidade))) :-
  solucoes(Inv, +(-prestador(IdUt,Nome,Especialidade,Instituicao,Cidade))::Inv, LInv),
  testa(LInv),
  %remover_impreciso(prestador(IdUt,Nome,Especialidade,Instituicao,Cidade)),
  assert((-prestador(IdUt,Nome,Especialidade,Instituicao,Cidade))),
  assert(perfeito(prestador(IdUt))).


% É procedimental, tal como os predicados de evolucao, solucoes, etc.

% Predicado que remove conhecimento impreciso relativo a um prestador
remover_impreciso(prestador(IdUt, Nome, Especialidade,Instituicao,Cidade)) :-
  retract(excecao(prestador(IdUt,_,_,_,_))),
  remover_impreciso(prestador(IdUt,Nome,Especialidade,Instituicao,Cidade)).

remover_impreciso(prestador(IdUt,Nome,Especialidade,Instituicao,Cidade)) :-
  retract(impreciso(prestador(IdUt))),
  remover_impreciso(prestador(IdUT,Nome,Especialidade,Instituicao,Cidade)).

remover_impreciso(prestador(IdUt, Nome, Especialidade,Instituicao,Cidade)) :-
  remover_incerto(prestador(IdUt,Nome,Especialidade,Instituicao,Cidade)).


% Predicado que remove conhecimento incerto relativo a um prestador
remover_incerto(prestador(IdUt,Nome,Especialidade,Instituicao,Cidade)) :-
  incerto_especialidade(prestador(IdUt,I)),
  retract((excecao(prestador(Id,N,Ida,M,C)) :-
    prestador(Id,N,I,M,C))),
  retract(prestador(IdUt, _, _ ,_,_)),
  retract(incerto_especialidade(prestador(IdUt, _))).

remover_incerto(prestador(IdUt,Nome,Especialidade,Instituicao,Cidade)) :-
  incerto_instituicao(prestador(IdUt,I)),
  retract((excecao(prestador(Id,N,Ida,M,C)) :-
    prestador(Id,N,Ida,I,C))),
  retract(prestador(IdUt, _, _ ,_,_)),
  retract(incerto_instituicao(prestador(IdUt, _))).

remover_incerto(prestador(IdUt,Nome,Especialidade,Instituicao,Cidade)) :-
  incerto_cidade(prestador(IdUt,I)),
  retract((excecao(prestador(Id,N,Ida,M),C) :-
    prestador(Id,N,Ida,M,I))),
  retract(prestador(IdUt, _, _ ,_,_)),
  retract(incerto_cidade(prestador(IdUt, _))).

remover_incerto(prestador(IdUt,Nome,Especialidade,Instituicao,Cidade)).

% Predicado que indica conhecimento incerto relativamente a prestadores
incerto(prestador(IdUt)) :-
  incerto_especialidade(prestador(IdUt, _)).
incerto(prestador(IdUt)) :-
  incerto_instituicao(prestador(IdUt, _)).
incerto(prestador(IdUt)) :-
  incerto_cidade(prestador(IdUt, _)).


% Evolucao de conhecimento impreciso que remove conhecimento incerto

%--------------------------------- - - - - - - - - - -  -  -  -  -   -
% Extensao do predicado evolucao_impreciso: EnumeracaoFactosAnomalos -> {V,F}

% Predicado que acrescenta conhecimento impreciso relativamente a prestadores
evolucao_impreciso([prestador(IdUt, Nome, Especialidade, Instituicao, Cidade)|T]) :-
  T \= [],
  same_prestador(T, IdUt),
  testaInvs([prestador(IdUt, Nome, Especialidade, Instituicao, Cidade)|T]),
  remover_incerto(prestador(IdUt, Nome, Especialidade, Instituicao, Cidade)),
  insere_excecoes([prestador(IdUt, Nome, Especialidade, Instituicao, Cidade)|T]).

% Predicado que verifica se dois prestadores são iguais
same_prestador([], _).
same_prestador([prestador(Id1, _, _, _, _) | T], Id2) :-
  Id1 == Id2,
  same_prestador(T, Id2).

% Predicado de teste a invariantes
testaInvs([]).
testaInvs([P|Ps]) :-
  solucoes(Inv, +P::Inv, LInv1),
  solucoes(Inv, +P:~:Inv, LInv2),
  testa(LInv1),  
  testa(LInv2),
  testaInvs(Ps).

% Predicado que insere exceções relativas a prestadores
insere_excecoes([]).
insere_excecoes([prestador(IdUt, Nome, Especialidade, Instituicao, Cidade)|Es]) :-
  assert(excecao(prestador(IdUt, Nome, Especialidade, Instituicao, Cidade))), 
  assert(impreciso(prestador(IdUt))),
  insere_excecoes(Es).

% ______________________________________________________________________________


% Predicado que acrescenta conhecimento incerto relativamente à especialidade de um prestador
evolucao_incerto_especialidade(prestador(IdUt, Nome, Especialidade, Instituicao, Cidade)) :-
  solucoes(Inv, +prestador(IdUt,Nome,Especialidade,Instituicao, Cidade):-:Inv, LInv1),
  solucoes(Inv, +prestador(IdUt, Nome, Especialidade, Instituicao, Cidade)::Inv, LInv2),
  testa(LInv1),
  testa(LInv2),
  assert((excecao(prestador(Id,N,I,M,C)) :-
         prestador(Id,N,Especialidade,M,C))),
  assert(prestador(IdUt, Nome, Especialidade, Instituicao, Cidade)),
  assert(incerto_especialidade(prestador(IdUt,Especialidade))).

% Predicado que acrescenta conhecimento interdito relativamente à especialidade de um prestador
evolucao_interdito_especialidade(prestador(IdUt, Nome, Especialidade, Instituicao, Cidade)) :-
  solucoes(Inv, +prestador(IdUt,Nome,Especialidade,Instituicao, Cidade):-:Inv, LInv1),
  solucoes(Inv, +prestador(IdUt, Nome, Especialidade, Instituicao, Cidade)::Inv, LInv2),
  testa(LInv1),
  testa(LInv2),
  assert(nulo(Especialidade)),
  assert((excecao(prestador(Id,N,E,I,C)) :-
         prestador(Id,N,Especialidade,I,C))),
  assert((+prestador(Id,N,E,I,C) :: (
               solucoes(Id,(prestador(Id,_,Especialidade,_,_), nulo(Especialidade)),S),
               comprimento(S,0)
             ))),
  assert(prestador(IdUt, Nome,Especialidade,Instituicao, Cidade)).

% Predicado que acrescenta conhecimento incerto relativamente à instituicao de um prestador
evolucao_incerto_instituicao(prestador(IdUt, Nome, Especialidade, Instituicao, Cidade)) :-
  solucoes(Inv, +prestador(IdUt,Nome,Especialidade,Instituicao, Cidade):-:Inv, LInv1),
  solucoes(Inv, +prestador(IdUt, Nome, Especialidade, Instituicao, Cidade)::Inv, LInv2),
  testa(LInv1),
  testa(LInv2),
  assert((excecao(prestador(Id,N,I,M,C)) :-
         prestador(Id,N,E,Instituicao,C))),
  assert(prestador(IdUt, Nome, Especialidade, Instituicao, Cidade)),
  assert(incerto_instituicao(prestador(IdUt,Instituicao))).

% Predicado que acrescenta conhecimento interdito relativamente à instituicao de um prestador
evolucao_interdito_instituicao(prestador(IdUt, Nome, Especialidade, Instituicao, Cidade)) :-
  solucoes(Inv, +prestador(IdUt,Nome,Especialidade,Instituicao, Cidade):-:Inv, LInv1),
  solucoes(Inv, +prestador(IdUt, Nome, Especialidade, Instituicao, Cidade)::Inv, LInv2),
  testa(LInv1),
  testa(LInv2),
  assert(nulo(Instituicao)),
  assert((excecao(prestador(Id,N,E,I,C)) :-
         prestador(Id,N,E,Instituicao,C))),
  assert((+prestador(Id,N,E,I,C) :: (
               solucoes(Id,(prestador(Id,_,_,Instituicao,_), nulo(Instituicao)),S),
               comprimento(S,0)
             ))),
  assert(prestador(IdUt, Nome,Especialidade,Instituicao, Cidade)).


% Predicado que acrescenta conhecimento incerto relativamente à cidade de um prestador
evolucao_incerto_cidade(prestador(IdUt, Nome, Especialidade, Instituicao, Cidade)) :-
  solucoes(Inv, +prestador(IdUt,Nome,Especialidade,Instituicao, Cidade):-:Inv, LInv1),
  solucoes(Inv, +prestador(IdUt, Nome, Especialidade, Instituicao, Cidade)::Inv, LInv2),
  testa(LInv1),
  testa(LInv2),
  assert((excecao(prestador(Id,N,I,M,C)) :-
         prestador(Id,N,E,I,Cidade))),
  assert(prestador(IdUt, Nome, Especialidade, Instituicao, Cidade)),
  assert(incerto_cidade(prestador(IdUt,Cidade))).


% Predicado que acrescenta conhecimento interdito relativamente à cidade de um prestador
evolucao_interdito_cidade(prestador(IdUt, Nome, Especialidade, Instituicao, Cidade)) :-
  solucoes(Inv, +prestador(IdUt,Nome,Especialidade,Instituicao, Cidade):-:Inv, LInv1),
  solucoes(Inv, +prestador(IdUt, Nome, Especialidade, Instituicao, Cidade)::Inv, LInv2),
  testa(LInv1),
  testa(LInv2),
  assert(nulo(Cidade)),
  assert((excecao(prestador(Id,N,E,I,C)) :-
         prestador(Id,N,E,I,Cidade))),
  assert((+prestador(Id,N,E,I,C) :: (
               solucoes(Id,(prestador(Id,_,_,_,Cidade), nulo(Cidade)),S),
               comprimento(S,0)
             ))),
  assert(prestador(IdUt, Nome,Especialidade,Instituicao, Cidade)).




% ______________________________________________________________________________
% ______________________________________________________________________________
% ______________________________________________________________________________

% EVOLUCAO CUIDADOS 
% IMPERFEITO -> Preco, Utente, Prestador ou Descricao

% Evolucao de conhecimento perfeito que remove conhecimento impreciso/incerto

% Predicado que acrescenta conhecimento perfeito relativo a um cuidado
evolucao_perfeito(cuidado(Id,Data,IdUt,IdPrest, Descricao, Preco)) :-
  solucoes(Inv, +cuidado(Id,Data,IdUt,IdPrest, Descricao, Preco)::Inv, LInv),
  testa(LInv),
  remover_impreciso(cuidado(Id,Data,IdUt,IdPrest, Descricao, Preco)),
  assert(cuidado(Id,Data,IdUt,IdPrest, Descricao, Preco)),
  assert(perfeito(cuidado(Id))).

% Predicado que acrescenta conhecimento perfeito relativo a um cuidado
evolucao_perfeito((-cuidado(Id,Data,IdUt,IdPrest, Descricao, Preco))) :-
  solucoes(Inv, +(-cuidado(Id,Data,IdUt,IdPrest, Descricao, Preco))::Inv, LInv),
  testa(LInv),
  %remover_impreciso(cuidado(Id,Data,IdUt,IdPrest, Descricao, Preco)),
  assert((-cuidado(Id,Data,IdUt,IdPrest, Descricao, Preco))),
  assert(perfeito(cuidado(Id))).


% Predicado que remove conhecimento impreciso relativo a um cuidado
remover_impreciso(cuidado(Id,Data,IdUt,IdPrest, Descricao, Preco)) :-
  retract(excecao(cuidado(Id,_,_,_,_,_))),
  remover_impreciso(cuidado(Id,Data,IdUt,IdPrest, Descricao, Preco)).

remover_impreciso(cuidado(Id,Data,IdUt,IdPrest, Descricao, Preco)) :-
  retract(impreciso(cuidado(Id))),
  remover_impreciso(cuidado(Id,Data,IdUt,IdPrest, Descricao, Preco)).

remover_impreciso(cuidado(Id,Data,IdUt,IdPrest, Descricao, Preco)) :-
  remover_incerto(cuidado(Id,Data,IdUt,IdPrest, Descricao, Preco)).


% Predicado que remove conhecimento incerto relativo a um cuidado
remover_incerto(cuidado(Id,Data,IdUt,IdPrest, Descricao, Preco)) :-
  incerto_data(cuidado(Id,D)),
  retract((excecao(cuidado(Id,Da,Ut,Prest,Desc,C)) :-
    cuidado(Id,D,Ut,Prest,Desc,C))),
  retract(cuidado(Id, _, _ ,_,_,_)),
  retract(incerto_data(cuidado(Id, _))).

remover_incerto(cuidado(Id,Data,IdUt,IdPrest, Descricao, Preco)) :-
  incerto_utente(cuidado(Id,U)),
  retract((excecao(cuidado(Id,Da,Ut,Prest,Desc,C)) :-
    cuidado(Id,Da,U,Prest,Desc,C))),
  retract(cuidado(Id, _, _ ,_,_,_)),
  retract(incerto_utente(cuidado(Id, _))).

remover_incerto(cuidado(Id,Data,IdUt,IdPrest, Descricao, Preco)) :-
  incerto_prestador(cuidado(Id,Prest)),
  retract((excecao(cuidado(Id,Da,Ut,Pre,Desc,C)) :-
    cuidado(Id,Da,Ut,Prest,Desc,C))),
  retract(cuidado(Id, _, _ ,_,_,_)),
  retract(incerto_prestador(cuidado(Id, _))).

remover_incerto(cuidado(Id,Data,IdUt,IdPrest, Descricao, Preco)) :-
  incerto_preco(cuidado(Id,Pre)),
  retract((excecao(cuidado(Id,Da,Ut,Pres,Desc,C)) :-
    cuidado(Id,Da,Ut,Prest,Desc,Pre))),
  retract(cuidado(Id, _, _ ,_,_,_)),
  retract(incerto_preco(cuidado(Id, _))).

remover_incerto(cuidado(Id,Data,IdUt,IdPrest, Descricao, Preco)) :-
  incerto_descricao(cuidado(Id,Des)),
  retract((excecao(cuidado(Id,Da,Ut,Pres,Desc,C)) :-
    cuidado(Id,Da,Ut,Prest,Des,Pre))),
  retract(cuidado(Id, _, _ ,_,_,_)),
  retract(incerto_descricao(cuidado(Id, _))).

remover_incerto(cuidado(Id,Data,IdUt,IdPrest, Descricao, Preco)).

% Predicado que indica conhecimento incerto relativamente a cuidados
incerto(cuidado(Id)) :-
  incerto_data(cuidado(Id, _)).
incerto(cuidado(Id)) :-
  incerto_utente(cuidado(Id, _)).
incerto(cuidado(Id)) :-
  incerto_prestador(cuidado(Id, _)).
incerto(cuidado(Id)) :-
  incerto_preco(cuidado(Id, _)).
incerto(cuidado(Id)) :-
  incerto_descricao(cuidado(Id, _)).


% Evolucao de conhecimento impreciso que remove conhecimento incerto

%--------------------------------- - - - - - - - - - -  -  -  -  -   -
% Extensao do predicado evolucao_impreciso: EnumeracaoFactosAnomalos -> {V,F}

% Predicado que acrescenta conhecimento impreciso relativamente a cuidados
evolucao_impreciso([cuidado(Id,Data,IdUt,IdPrest, Descricao, Preco)|T]) :-
  T \= [],
  same_cuidado(T, Id),
  testaInvs([cuidado(Id,Data,IdUt,IdPrest, Descricao, Preco)|T]),
  remover_incerto(cuidado(Id,Data,IdUt,IdPrest, Descricao, Preco)),
  insere_excecoes([cuidado(Id,Data,IdUt,IdPrest, Descricao, Preco)|T]).

% Predicado que verifica se dois cuidados são iguais
same_cuidado([], _).
same_cuidado([cuidado(Id1, _, _, _,_,_) | T], Id2) :-
  Id1 == Id2,
  same_cuidado(T, Id2).

% Predicado que insere exceções relativas a cuidados
insere_excecoes([]).
insere_excecoes([cuidado(Id,Data,IdUt,IdPrest, Descricao, Preco)|Es]) :-
  assert(excecao(cuidado(Id,Data,IdUt,IdPrest, Descricao, Preco))), 
  assert(impreciso(cuidado(Id))),
  insere_excecoes(Es).


% Predicado que acrescenta conhecimento incerto relativamente à data de um cuidado
evolucao_incerto_data(cuidado(Id,Data,IdUt,IdPrest, Descricao, Preco)) :-
  solucoes(Inv, +cuidado(Id,Data,IdUt,IdPrest, Descricao, Preco) :-: Inv, LInv1),
  solucoes(Inv, +cuidado(Id,Data,IdUt,IdPrest, Descricao, Preco)::Inv, LInv2),
  testa(LInv1),
  testa(LInv2),
  assert((excecao(cuidado(I,D,U,P,De,Pre)) :- 
    cuidado(I,Data,U,P,De,Pre))),
  assert(cuidado(Id,Data,IdUt,IdPrest, Descricao, Preco)),
  assert(incerto_data(cuidado(Id,Data))).


% Predicado que acrescenta conhecimento interdito relativamente à data de um cuidado
evolucao_interdito_data(cuidado(Id,Data,IdUt,IdPrest, Descricao, Preco)) :-
  solucoes(Inv, +cuidado(Id,Data,IdUt,IdPrest, Descricao, Preco):-:Inv, LInv1),
  solucoes(Inv, +cuidado(Id,Data,IdUt,IdPrest, Descricao, Preco)::Inv, LInv2),
  testa(LInv1),
  testa(LInv2),
  assert(nulo(Data)),
  assert((excecao(cuidado(I,D,U,P,Des,Pre)) :- 
    cuidado(I,Data,U,P,Des,Pre))),
  assert((+cuidado(I,D,U,P,Des,Pre) :: (
      solucoes(I,(cuidado(I,Data,_,_,_,_), nulo(Data)),S),
      comprimento(S,0)))),
  assert(cuidado(Id,Data,IdUt,IdPrest, Descricao, Preco)).


% Predicado que acrescenta conhecimento incerto relativamente ao utente de um cuidado
evolucao_incerto_utente(cuidado(Id,Data,IdUt,IdPrest, Descricao, Preco)) :-
  solucoes(Inv, +cuidado(Id,Data,IdUt,IdPrest, Descricao, Preco) :-: Inv, LInv1),
  %solucoes(Inv, +cuidado(Id,Data,IdUt,IdPrest, Descricao, Preco)::Inv, LInv2),
  solucoes(Inv, +cuidado(Id,Data,IdUt,IdPrest, Descricao, Preco):*:Inv, LInv2),
  testa(LInv1),
  testa(LInv2),
  assert((excecao(cuidado(I,D,U,P,De,Pre)) :- 
    cuidado(I,D,IdUt,P,De,Pre))),
  assert(cuidado(Id,Data,IdUt,IdPrest, Descricao, Preco)),
  assert(incerto_utente(cuidado(Id,IdUt))).

% Predicado que acrescenta conhecimento interdito relativamente ao utente de um cuidado
evolucao_interdito_utente(cuidado(Id,Data,IdUt,IdPrest, Descricao, Preco)) :-
  solucoes(Inv, +cuidado(Id,Data,IdUt,IdPrest, Descricao, Preco):-:Inv, LInv1),
  %solucoes(Inv, +cuidado(Id,Data,IdUt,IdPrest, Descricao, Preco)::Inv, LInv2),
  solucoes(Inv, +cuidado(Id,Data,IdUt,IdPrest, Descricao, Preco):*:Inv, LInv2),
  testa(LInv1),
  testa(LInv2),
  assert(nulo(IdUt)),
  assert((excecao(cuidado(I,D,U,P,Des,Pre)) :- 
    cuidado(I,D,IdUt,P,Des,Pre))),
  assert((+cuidado(I,D,U,P,Des,Pre) :: (
      solucoes(I,(cuidado(I,_,IdUt,_,_,_), nulo(IdUt)),S),
      comprimento(S,0)))),
  assert((+cuidado(I,D,U,P,Des,Pre) :*: (
      solucoes(I,(cuidado(I,_,IdUt,_,_,_), nulo(IdUt)),S),
      comprimento(S,0)))),
  assert((+cuidado(I,D,U,P,Des,Pre) :+: (
      solucoes(I,(cuidado(I,_,IdUt,_,_,_), nulo(IdUt)),S),
      comprimento(S,0)))),
  assert(cuidado(Id,Data,IdUt,IdPrest, Descricao, Preco)).


% Predicado que acrescenta conhecimento incerto relativamente ao prestador de um cuidado
evolucao_incerto_prestador(cuidado(Id,Data,IdUt,IdPrest, Descricao, Preco)) :-
  solucoes(Inv, +cuidado(Id,Data,IdUt,IdPrest, Descricao, Preco) :-: Inv, LInv1),
  %solucoes(Inv, +cuidado(Id,Data,IdUt,IdPrest, Descricao, Preco)::Inv, LInv2),
  solucoes(Inv, +cuidado(Id,Data,IdUt,IdPrest, Descricao, Preco):+:Inv, LInv2),
  testa(LInv1),
  testa(LInv2),
  assert((excecao(cuidado(I,D,U,P,De,Pre)) :- 
    cuidado(I,D,U,IdPrest,De,Pre))),
  assert(cuidado(Id,Data,IdUt,IdPrest, Descricao, Preco)),
  assert(incerto_prestador(cuidado(Id,IdPrest))).

% Predicado que acrescenta conhecimento interdito relativamente ao prestador de um cuidado
evolucao_interdito_prestador(cuidado(Id,Data,IdUt,IdPrest, Descricao, Preco)) :-
  solucoes(Inv, +cuidado(Id,Data,IdUt,IdPrest, Descricao, Preco):-:Inv, LInv1),
  %solucoes(Inv, +cuidado(Id,Data,IdUt,IdPrest, Descricao, Preco)::Inv, LInv2),
  solucoes(Inv, +cuidado(Id,Data,IdUt,IdPrest, Descricao, Preco):+:Inv, LInv2),
  testa(LInv1),
  testa(LInv2),
  assert(nulo(IdPrest)),
  assert((excecao(cuidado(I,D,U,P,Des,Pre)) :- 
    cuidado(I,D,U,IdPrest,Des,Pre))),
  assert((+cuidado(I,D,U,P,Des,Pre) :: (
      solucoes(I,(cuidado(I,_,_,IdPrest,_,_), nulo(IdPrest)),S),
      comprimento(S,0)))),
  assert((+cuidado(I,D,U,P,Des,Pre) :*: (
      solucoes(I,(cuidado(I,_,_,IdPrest,_,_), nulo(IdPrest)),S),
      comprimento(S,0)))),
  assert((+cuidado(I,D,U,P,Des,Pre) :+: (
      solucoes(I,(cuidado(I,_,_,IdPrest,_,_), nulo(IdPrest)),S),
      comprimento(S,0)))),
  assert(cuidado(Id,Data,IdUt,IdPrest, Descricao, Preco)).


% Predicado que acrescenta conhecimento incerto relativamente à descrição de um cuidado
evolucao_incerto_descricao(cuidado(Id,Data,IdUt,IdPrest, Descricao, Preco)) :-
  solucoes(Inv, +cuidado(Id,Data,IdUt,IdPrest, Descricao, Preco) :-: Inv, LInv1),
  solucoes(Inv, +cuidado(Id,Data,IdUt,IdPrest, Descricao, Preco)::Inv, LInv2),
  testa(LInv1),
  testa(LInv2),
  assert((excecao(cuidado(I,D,U,P,De,Pre)) :- 
    cuidado(I,D,U,P,Descricao,Pre))),
  assert(cuidado(Id,Data,IdUt,IdPrest, Descricao, Preco)),
  assert(incerto_descricao(cuidado(Id,Descricao))).


% Predicado que acrescenta conhecimento interdito relativamente à descrição de um cuidado
evolucao_interdito_descricao(cuidado(Id,Data,IdUt,IdPrest, Descricao, Preco)) :-
  solucoes(Inv, +cuidado(Id,Data,IdUt,IdPrest, Descricao, Preco):-:Inv, LInv1),
  solucoes(Inv, +cuidado(Id,Data,IdUt,IdPrest, Descricao, Preco)::Inv, LInv2),
  testa(LInv1),
  testa(LInv2),
  assert(nulo(Descricao)),
  assert((excecao(cuidado(I,D,U,P,Des,Pre)) :- 
    cuidado(I,D,U,P,Descricao,Pre))),
  assert((+cuidado(I,D,U,P,Des,Pre) :: (
      solucoes(I,(cuidado(I,_,_,_,Descricao,_), nulo(Descricao)),S),
      comprimento(S,0)))),
  assert(cuidado(Id,Data,IdUt,IdPrest, Descricao, Preco)).


% Predicado que acrescenta conhecimento incerto relativamente ao preço de um cuidado
evolucao_incerto_preco(cuidado(Id,Data,IdUt,IdPrest, Descricao, Preco)) :-
  solucoes(Inv, +cuidado(Id,Data,IdUt,IdPrest, Descricao, Preco) :-: Inv, LInv1),
  solucoes(Inv, +cuidado(Id,Data,IdUt,IdPrest, Descricao, Preco)::Inv, LInv2),
  testa(LInv1),
  testa(LInv2),
  assert((excecao(cuidado(I,D,U,P,De,Pre)) :- 
    cuidado(I,D,U,P,De,Preco))),
  assert(cuidado(Id,Data,IdUt,IdPrest, Descricao, Preco)),
  assert(incerto_preco(cuidado(Id,Preco))).


% Predicado que acrescenta conhecimento interdito relativamente ao preço de um cuidado
evolucao_interdito_preco(cuidado(Id,Data,IdUt,IdPrest, Descricao, Preco)) :-
  solucoes(Inv, +cuidado(Id,Data,IdUt,IdPrest, Descricao, Preco):-:Inv, LInv1),
  solucoes(Inv, +cuidado(Id,Data,IdUt,IdPrest, Descricao, Preco)::Inv, LInv2),
  testa(LInv1),
  testa(LInv2),
  assert(nulo(Preco)),
  assert((excecao(cuidado(I,D,U,P,Des,Pre)) :- 
    cuidado(I,D,U,P,Des,Preco))),
  assert((+cuidado(I,D,U,P,Des,Pre) :: (
      solucoes(I,(cuidado(I,_,_,_,_,Preco), nulo(Preco)),S),
      comprimento(S,0)))),
  assert(cuidado(Id,Data,IdUt,IdPrest, Descricao, Preco)).



% ______________________________________________________________________________
% ______________________________________________________________________________
% ______________________________________________________________________________

% INVOLUCAO UTENTES

% Extensao do predicado involucao_perfeito: ConhecimentoAremover -> {V,F}

% Involução do conhecimento perfeito relativo a um utente
involucao_perfeito(utente(IdUt, Nome, Idade, Morada)) :-
  utente(IdUt, Nome, Idade, Morada),
  solucoes(Inv, -utente(IdUt,Nome,Idade,Morada)::Inv, LInv),
  testa(LInv),
  retract(utente(IdUt, Nome, Idade, Morada)),
  retract(perfeito(utente(IdUt))).

% Involução do conhecimento perfeito relativo a um utente
involucao_perfeito((-utente(IdUt, Nome, Idade, Morada))) :-
  utente(IdUt, Nome, Idade, Morada),
  solucoes(Inv, -(-utente(IdUt,Nome,Idade,Morada))::Inv, LInv),
  testa(LInv),
  retract(utente(IdUt, Nome, Idade, Morada)),
  retract(perfeito(utente(IdUt))).

% Involução do conhecimento incerto relativo à idade de um utente
involucao_incerto_idade(utente(IdUt, Nome, Idade, Morada)) :-
  utente(IdUt, Nome,Idade,Morada),
  incerto_idade(utente(IdUt, I)),
  solucoes(Inv, -utente(IdUt, Nome, Idade, Morada)::Inv, LInv),
  testa(LInv),
  retract((excecao(utente(Id,N,Ida,M)) :-
    utente(Id,N,I,M))),
  retract(utente(IdUt, _, _ ,_)),
  retract(incerto_idade(utente(IdUt, _))).

% Involução do conhecimento incerto relativo à morada de um utente
involucao_incerto_morada(utente(IdUt, Nome, Idade, Morada)) :-
  utente(IdUt, Nome,Idade,Morada),
  incerto_morada(utente(IdUt, M)),
  solucoes(Inv, -utente(IdUt, Nome, Idade, Morada)::Inv, LInv),
  testa(LInv),
  retract((excecao(utente(Id,N,I,Mor)) :-
    utente(Id,N,I,M))),
  retract(utente(IdUt, _, _ ,_)),
  retract(incerto_morada(utente(IdUt, _))).

%--------------------------------- - - - - - - - - - -  -  -  -  -   -
% Extensao do predicado involucao_impreciso: EnumeracaoFactosAnomalos -> {V,F}

% Involução do conhecimento impreciso relativo a utentes
involucao_impreciso([utente(Id,Nome,Idade,Morada) | T]) :-
    procuraPor([utente(Id,Nome,Idade,Morada) | T]),
    same_utente(T, Id),
    testaInvolInvs([utente(Id,Nome,Idade,Morada) | T]),
    removeExcecoes([utente(Id,Nome,Idade,Morada) | T]).

% Remove a excecao a cada um dos predicados de uma lista de predicados
removeExcecoes([]).
removeExcecoes([utente(IdUt,Nome,Idade,Morada)|Ps]) :-
  retract(excecao(utente(IdUt, Nome, Idade, Morada))),
  retract(impreciso(utente(IdUt))),
  removeExcecoes(Ps).

% Procura por uma excecao para cada um dos termos de uma lista de termos
procuraPor([]).
procuraPor([T|Ts]) :-
    excecao(T), procuraPor(Ts).

% Testa os invariantes de remoção de uma lista para cada um 
% dos elementos de uma lista de predicados
testaInvolInvs([]).
testaInvolInvs([P|Ps]) :- 
    solucoes(Inv, -P::Inv, LInv),
    testa(LInv),
    testaInvolInvs(Ps).

% Involucao do conhecimento interdito relativo a idade de um utente
involucao_interdito_idade(utente(IdUt, Nome, Idade, Morada)) :-
  utente(IdUt, Nome, Idade, Morada),
  nulo(Idade),
  solucoes(Inv, -utente(IdUt, Nome, Idade, Morada)::Inv, LInv),
  testa(LInv),
  retract(nulo(Idade)),
  retract((excecao(utente(Id,N,I,M)) :-
         utente(Id,N,Idade,M))),
  retract((+utente(Id,N,I,M) :: (
               solucoes(Id,(utente(Id,_,Idade,_), nulo(Idade)),S),
               comprimento(S,0)
             ))),
  retract(utente(IdUt, Nome,Idade,Morada)).

% Involucao do conhecimento interdito relativo à morada de um utente
involucao_interdito_morada(utente(IdUt, Nome, Idade, Morada)) :-
  utente(IdUt, Nome, Idade, Morada),
  nulo(Morada),
  solucoes(Inv, -utente(IdUt, Nome, Idade, Morada)::Inv, LInv),
  testa(LInv),
  retract(nulo(Morada)),
  retract((excecao(utente(Id,N,I,M)) :-
         utente(Id,N,I,Morada))),
  retract((+utente(Id,N,I,M) :: (
               solucoes(Id,(utente(Id,_,_,Morada), nulo(Morada)),S),
               comprimento(S,0)
             ))),
  retract(utente(IdUt, Nome,Idade,Morada)).


% ______________________________________________________________________________
% ______________________________________________________________________________
% ______________________________________________________________________________

% INVOLUCAO PRESTADORES 

% Extensao do predicado involucao_perfeito: ConhecimentoAremover -> {V,F}

% Involução do conhecimento perfeito relativo a um prestador
involucao_perfeito(prestador(IdUt, Nome, Especialidade, Instituicao, Cidade)) :-
  prestador(IdUt, Nome, Especialidade, Instituicao, Cidade),
  solucoes(Inv, -prestador(IdUt,Nome,Especialidade,Instituicao, Cidade)::Inv, LInv),
  testa(LInv),
  retract(prestador(IdUt, Nome, Especialidade, Instituicao, Cidade)),
  retract(perfeito(prestador(IdUt))).

% Involução do conhecimento perfeito relativo a um prestador
involucao_perfeito((-prestador(IdUt, Nome, Especialidade, Instituicao, Cidade))) :-
  prestador(IdUt, Nome, Especialidade, Instituicao, Cidade),
  solucoes(Inv, -(-prestador(IdUt,Nome,Especialidade,Instituicao, Cidade))::Inv, LInv),
  testa(LInv),
  retract(prestador(IdUt, Nome, Especialidade, Instituicao, Cidade)),
  retract(perfeito(prestador(IdUt))).

% Involução do conhecimento incerto relativo à especialidade de um prestador
involucao_incerto_especialidade(prestador(IdUt, Nome, Especialidade, Instituicao, Cidade)) :-
  prestador(IdUt, Nome,Especialidade,Instituicao, Cidade),
  incerto_especialidade(prestador(IdUt, E)),
  solucoes(Inv, -prestador(IdUt, Nome, Especialidade, Instituicao, Cidade)::Inv, LInv),
  testa(LInv),
  retract((excecao(prestador(Id,N,Esp,I,C)) :-
    prestador(Id,N,E,I,C))),
  retract(prestador(IdUt, _, _ ,_,_)),
  retract(incerto_especialidade(prestador(IdUt, _))).


% Involução do conhecimento incerto relativo à instituicao de um prestador
involucao_incerto_instituicao(prestador(IdUt, Nome, Especialidade, Instituicao, Cidade)) :-
  prestador(IdUt, Nome,Especialidade,Instituicao, Cidade),
  incerto_instituicao(prestador(IdUt, I)),
  solucoes(Inv, -prestador(IdUt, Nome, Especialidade, Instituicao, Cidade)::Inv, LInv),
  testa(LInv),
  retract((excecao(prestador(Id,N,E,Inst,C)) :-
    prestador(Id,N,E,I,C))),
  retract(prestador(IdUt, _, _ ,_,_)),
  retract(incerto_instituicao(prestador(IdUt, _))).

% Involução do conhecimento incerto relativo à cidade de um prestador
involucao_incerto_cidade(prestador(IdUt, Nome, Especialidade, Instituicao, Cidade)) :-
  prestador(IdUt, Nome,Especialidade,Instituicao, Cidade),
  incerto_cidade(prestador(IdUt, C)),
  solucoes(Inv, -prestador(IdUt, Nome, Especialidade, Instituicao, Cidade)::Inv, LInv),
  testa(LInv),
  retract((excecao(prestador(Id,N,E,I,Cid)) :-
    prestador(Id,N,E,I,C))),
  retract(prestador(IdUt, _, _ ,_,_)),
  retract(incerto_cidade(prestador(IdUt, _))).

%--------------------------------- - - - - - - - - - -  -  -  -  -   -
% Extensao do predicado involucao_impreciso: EnumeracaoFactosAnomalos -> {V,F}

% Involução do conhecimento impreciso relativo a prestadores
involucao_impreciso([prestador(Id,Nome,Especialidade,Instituicao, Cidade) | T]) :-
    procuraPor([prestador(Id,Nome,Especialidade,Instituicao, Cidade) | T]),
    same_prestador(T, Id),
    testaInvolInvs([prestador(Id,Nome,Especialidade,Instituicao, Cidade) | T]),
    removeExcecoes([prestador(Id,Nome,Especialidade,Instituicao, Cidade) | T]).

% Remove a excecao a cada um dos predicados de uma lista de predicados
removeExcecoes([prestador(IdUt,Nome,Especialidade,Instituicao, Cidade)|Ps]) :-
  retract(excecao(prestador(IdUt, Nome, Especialidade,Instituicao, Cidade))),
  retract(impreciso(prestador(IdUt))),
  removeExcecoes(Ps).


% Involucao do conhecimento interdito relativo à especialidade de um prestador
involucao_interdito_especialidade(prestador(IdUt, Nome, Especialidade, Instituicao, Cidade)) :-
  prestador(IdUt, Nome, Especialidade, Instituicao, Cidade),
  nulo(Especialidade),
  solucoes(Inv, -prestador(IdUt, Nome, Especialidade, Instituicao, Cidade)::Inv, LInv),
  testa(LInv),
  retract(nulo(Especialidade)),
  retract((excecao(prestador(Id,N,E,I,C)) :-
         prestador(Id,N,Especialidade,I,C))),
  retract((+prestador(Id,N,E,I,C) :: (
               solucoes(Id,(prestador(Id,_,Especialidade,_,_), nulo(Especialidade)),S),
               comprimento(S,0)
             ))),
  retract(prestador(IdUt, Nome,Especialidade,Instituicao, Cidade)).

% Involucao do conhecimento interdito relativo à instituicao de um prestador
involucao_interdito_instituicao(prestador(IdUt, Nome, Especialidade, Instituicao, Cidade)) :-
  prestador(IdUt, Nome, Especialidade, Instituicao, Cidade),
  nulo(Instituicao),
  solucoes(Inv, -prestador(IdUt, Nome, Especialidade, Instituicao, Cidade)::Inv, LInv),
  testa(LInv),
  retract(nulo(Instituicao)),
  retract((excecao(prestador(Id,N,E,I,C)) :-
         prestador(Id,N,E,Instituicao,C))),
  retract((+prestador(Id,N,E,I,C) :: (
               solucoes(Id,(prestador(Id,_,_,Instituicao,_), nulo(Instituicao)),S),
               comprimento(S,0)
             ))),
  retract(prestador(IdUt, Nome,Especialidade,Instituicao, Cidade)).

% Involucao do conhecimento interdito relativo à cidade de um prestador
involucao_interdito_cidade(prestador(IdUt, Nome, Especialidade, Instituicao, Cidade)) :-
  prestador(IdUt, Nome, Especialidade, Instituicao, Cidade),
  nulo(Cidade),
  solucoes(Inv, -prestador(IdUt, Nome, Especialidade, Instituicao, Cidade)::Inv, LInv),
  testa(LInv),
  retract(nulo(Cidade)),
  retract((excecao(prestador(Id,N,E,I,C)) :-
         prestador(Id,N,E,I,Cidade))),
  retract((+prestador(Id,N,E,I,C) :: (
               solucoes(Id,(prestador(Id,_,_,_,Cidade), nulo(Cidade)),S),
               comprimento(S,0)
             ))),
  retract(prestador(IdUt, Nome,Especialidade,Instituicao, Cidade)).

% ______________________________________________________________________________
% ______________________________________________________________________________
% ______________________________________________________________________________

% INVOLUCAO CUIDADOS 


% Extensao do predicado involucao_perfeito: ConhecimentoAremover -> {V,F}

% Involução do conhecimento perfeito relativo a um cuidado
involucao_perfeito(cuidado(Id,Data,IdUt,IdPrest, Descricao, Preco)) :-
  cuidado(Id,Data,IdUt,IdPrest, Descricao, Preco),
  solucoes(Inv, -cuidado(Id,Data,IdUt,IdPrest, Descricao, Preco)::Inv, LInv),
  testa(LInv),
  retract(cuidado(Id,Data,IdUt,IdPrest, Descricao, Preco)),
  retract(perfeito(cuidado(Id))).

% Involução do conhecimento perfeito relativo a um cuidado
involucao_perfeito((-cuidado(Id,Data,IdUt,IdPrest, Descricao, Preco))) :-
  cuidado(Id,Data,IdUt,IdPrest, Descricao, Preco),
  solucoes(Inv, -(-cuidado(Id,Data,IdUt,IdPrest, Descricao, Preco))::Inv, LInv),
  testa(LInv),
  retract(cuidado(Id,Data,IdUt,IdPrest, Descricao, Preco)),
  retract(perfeito(cuidado(Id))).

% Involução do conhecimento incerto relativo à data de um cuidado
involucao_incerto_data(cuidado(Id,Data,IdUt,IdPrest, Descricao, Preco)) :- 
  cuidado(Id,Data,IdUt,IdPrest, Descricao, Preco),
  incerto_data(cuidado(Id,D)),
  solucoes(Inv,-cuidado(Id,Data,IdUt,IdPrest, Descricao, Preco)::Inv,LInv),
  testa(LInv),
  retract((excecao(cuidado(I,Da,U,P,Des,Pre)) :-
    cuidado(I,D,U,P,Des,Pre))),
  retract(cuidado(Id,_,_,_,_,_)),
  retract(incerto_data(cuidado(Id,_))).

% Involução do conhecimento incerto relativo ao utente de um cuidado
involucao_incerto_utente(cuidado(Id,Data,IdUt,IdPrest, Descricao, Preco)) :- 
  cuidado(Id,Data,IdUt,IdPrest, Descricao, Preco),
  incerto_utente(cuidado(Id,U)),
  solucoes(Inv,-cuidado(Id,Data,IdUt,IdPrest, Descricao, Preco)::Inv,LInv),
  testa(LInv),
  retract((excecao(cuidado(I,Da,Ut,P,Des,Pre)) :-
    cuidado(I,Da,U,P,Des,Pre))),
  retract(cuidado(Id,_,_,_,_,_)),
  retract(incerto_utente(cuidado(Id,_))).

% Involução do conhecimento incerto relativo ao prestador de um cuidado
involucao_incerto_prestador(cuidado(Id,Data,IdUt,IdPrest, Descricao, Preco)) :- 
  cuidado(Id,Data,IdUt,IdPrest, Descricao, Preco),
  incerto_prestador(cuidado(Id,P)),
  solucoes(Inv,-cuidado(Id,Data,IdUt,IdPrest, Descricao, Preco)::Inv,LInv),
  testa(LInv),
  retract((excecao(cuidado(I,Da,U,Pr,Des,Pre)) :-
    cuidado(I,Da,U,P,Des,Pre))),
  retract(cuidado(Id,_,_,_,_,_)),
  retract(incerto_prestador(cuidado(Id,_))).

% Involução do conhecimento incerto relativo à descrição de um cuidado
involucao_incerto_descricao(cuidado(Id,Data,IdUt,IdPrest, Descricao, Preco)) :- 
  cuidado(Id,Data,IdUt,IdPrest, Descricao, Preco),
  incerto_descricao(cuidado(Id,D)),
  solucoes(Inv,-cuidado(Id,Data,IdUt,IdPrest, Descricao, Preco)::Inv,LInv),
  testa(LInv),
  retract((excecao(cuidado(I,Da,U,P,Des,Pre)) :-
    cuidado(I,Da,U,P,D,Pre))),
  retract(cuidado(Id,_,_,_,_,_)),
  retract(incerto_descricao(cuidado(Id,_))).

% Involução do conhecimento incerto relativo ao preço de um cuidado
involucao_incerto_preco(cuidado(Id,Data,IdUt,IdPrest, Descricao, Preco)) :- 
  cuidado(Id,Data,IdUt,IdPrest, Descricao, Preco),
  incerto_preco(cuidado(Id,Prec)),
  solucoes(Inv,-cuidado(Id,Data,IdUt,IdPrest, Descricao, Preco)::Inv,LInv),
  testa(LInv),
  retract((excecao(cuidado(I,Da,U,P,D,Pre)) :-
    cuidado(I,Da,U,P,D,Prec))),
  retract(cuidado(Id,_,_,_,_,_)),
  retract(incerto_preco(cuidado(Id,_))).

%--------------------------------- - - - - - - - - - -  -  -  -  -   -
% Extensao do predicado involucao_impreciso: EnumeracaoFactosAnomalos -> {V,F}

% Involução do conhecimento impreciso relativo a cuidados
involucao_impreciso([cuidado(Id,Data,IdUt,IdPrest, Descricao, Preco) | T]) :-
    procuraPor([cuidado(Id,Data,IdUt,IdPrest, Descricao, Preco) | T]),
    same_cuidado(T, Id),
    testaInvolInvs([cuidado(Id,Data,IdUt,IdPrest, Descricao, Preco) | T]),
    removeExcecoes([cuidado(Id,Data,IdUt,IdPrest, Descricao, Preco) | T]).

% Remove a excecao a cada um dos predicados de uma lista de predicados
removeExcecoes([cuidado(Id,Data,IdUt,IdPrest, Descricao, Preco)|Ps]) :-
  retract(excecao(cuidado(Id,Data,IdUt,IdPrest, Descricao, Preco))),
  retract(impreciso(cuidado(Id))),
  removeExcecoes(Ps).



% Involucao do conhecimento interdito relativo à data de um cuidado
involucao_interdito_data(cuidado(Id,Data,IdUt,IdPrest, Descricao, Preco)) :-
  cuidado(Id,Data,IdUt,IdPrest, Descricao, Preco),
  nulo(Data),
  solucoes(Inv, -cuidado(Id,Data,IdUt,IdPrest, Descricao, Preco)::Inv, LInv),
  testa(LInv),
  retract(nulo(Data)),
  retract((excecao(cuidado(I,D,U,P,Des,Pre)) :- 
      cuidado(I,Data,U,P,Desc,Pre))),
  retract((+cuidado(I,D,U,P,Des,Pre) :: (
      solucoes(I,(cuidado(I,Data,_,_,_,_), nulo(Data)),S),
      comprimento(S,0)))),
  retract(cuidado(Id,Data,IdUt,IdPrest, Descricao, Preco)).

% Involucao do conhecimento interdito relativo ao utente de um cuidado
involucao_interdito_utente(cuidado(Id,Data,IdUt,IdPrest, Descricao, Preco)) :-
  cuidado(Id,Data,IdUt,IdPrest, Descricao, Preco),
  nulo(IdUt),
  solucoes(Inv, -cuidado(Id,Data,IdUt,IdPrest, Descricao, Preco)::Inv, LInv),
  testa(LInv),
  retract(nulo(IdUt)),
  retract((excecao(cuidado(I,D,U,P,Des,Pre)) :- 
      cuidado(I,D,IdUt,P,Desc,Pre))),
  retract((+cuidado(I,D,U,P,Des,Pre) :: (
      solucoes(I,(cuidado(I,_,IdUt,_,_,_), nulo(IdUt)),S),
      comprimento(S,0)))),
  retract((+cuidado(I,D,U,P,Des,Pre) :+: (
      solucoes(I,(cuidado(I,_,IdUt,_,_,_), nulo(IdUt)),S),
      comprimento(S,0)))),
  retract((+cuidado(I,D,U,P,Des,Pre) :*: (
      solucoes(I,(cuidado(I,_,IdUt,_,_,_), nulo(IdUt)),S),
      comprimento(S,0)))),
  retract(cuidado(Id,Data,IdUt,IdPrest, Descricao, Preco)).

% Involucao do conhecimento interdito relativo ao prestador de um cuidado
involucao_interdito_prestador(cuidado(Id,Data,IdUt,IdPrest, Descricao, Preco)) :-
  cuidado(Id,Data,IdUt,IdPrest, Descricao, Preco),
  nulo(IdPrest),
  solucoes(Inv, -cuidado(Id,Data,IdUt,IdPrest, Descricao, Preco)::Inv, LInv),
  testa(LInv),
  retract(nulo(IdPrest)),
  retract((excecao(cuidado(I,D,U,P,Des,Pre)) :- 
      cuidado(I,D,U,IdPrest,Desc,Pre))),
  retract((+cuidado(I,D,U,P,Des,Pre) :: (
      solucoes(I,(cuidado(I,_,_,IdPrest,_,_), nulo(IdPrest)),S),
      comprimento(S,0)))),
  retract((+cuidado(I,D,U,P,Des,Pre) :+: (
      solucoes(I,(cuidado(I,_,_,IdPrest,_,_), nulo(IdPrest)),S),
      comprimento(S,0)))),
  retract((+cuidado(I,D,U,P,Des,Pre) :*: (
      solucoes(I,(cuidado(I,_,_,IdPrest,_,_), nulo(IdPrest)),S),
      comprimento(S,0)))),
  retract(cuidado(Id,Data,IdUt,IdPrest, Descricao, Preco)).

% Involucao do conhecimento interdito relativo à descrição de um cuidado
involucao_interdito_descricao(cuidado(Id,Data,IdUt,IdPrest, Descricao, Preco)) :-
  cuidado(Id,Data,IdUt,IdPrest, Descricao, Preco),
  nulo(Descricao),
  solucoes(Inv, -cuidado(Id,Data,IdUt,IdPrest, Descricao, Preco)::Inv, LInv),
  testa(LInv),
  retract(nulo(Descricao)),
  retract((excecao(cuidado(I,D,U,P,Des,Pre)) :- 
      cuidado(I,D,U,P,Descricao,Pre))),
  retract((+cuidado(I,D,U,P,Des,Pre) :: (
      solucoes(I,(cuidado(I,_,_,_,Descricao,_), nulo(Descricao)),S),
      comprimento(S,0)))),
  retract(cuidado(Id,Data,IdUt,IdPrest, Descricao, Preco)).

% Involucao do conhecimento interdito relativo ao preço de um cuidado
involucao_interdito_preco(cuidado(Id,Data,IdUt,IdPrest, Descricao, Preco)) :-
  cuidado(Id,Data,IdUt,IdPrest, Descricao, Preco),
  nulo(Preco),
  solucoes(Inv, -cuidado(Id,Data,IdUt,IdPrest, Descricao, Preco)::Inv, LInv),
  testa(LInv),
  retract(nulo(Preco)),
  retract((excecao(cuidado(I,D,U,P,Des,Pre)) :- 
      cuidado(I,D,U,P,Des,Preco))),
  retract((+cuidado(I,D,U,P,Des,Pre) :: (
      solucoes(I,(cuidado(I,_,_,_,_,Preco), nulo(Preco)),S),
      comprimento(S,0)))),
  retract(cuidado(Id,Data,IdUt,IdPrest, Descricao, Preco)).



% NAO LIGAR A ISTO AINDA 

%--------------------------------- - - - - - - - - - -  -  -  -  -   -
% ------------------------- CONHECIMENTO NEGATIVO ---------------------------- %
%--------------------------------- - - - - - - - - - -  -  -  -  -   -
% Conhecimento perfeito negativo

-utente(100, bernardino, 29, braga).
perfeito(utente(100)).

-prestador(34, carlos_antonio, pneumologia, centro_de_saude_de_gualtar, braga).
perfeito(prestador(34)).

-cuidado(9,09-01-2017, 1, 3, consulta_rotina ,75).
perfeito(cuidado(9)).

% É falsa a informação de que certos utentes/prestador tenham estado/trabalhem no centro de Saúde
-utente(11, miguel, 22, mafra).
perfeito(utente(11)).
-utente(12, marta, 33, oeiras).
perfeito(utente(12)).
-utente(13, fatima, 32, faro).
perfeito(utente(13)).

-prestador(11, veronica_silva, imunoalergologia, publico, braganca).
perfeito(prestador(11)).
-prestador(12, nicole_castro, ortopedia, privado, barcelos).
perfeito(prestador(12)).
-prestador(13, judite_sousa, pneumologia, publico, alentejo).
perfeito(prestador(13)).

%--------------------------------- - - - - - - - - - -  -  -  -  -   -
% Representação de conhecimento imperfeito

% Tipo I. Conhecimento Incerto

cuidado(8,04-04-2017, 1, 2, consulta_rotina, nulo1).
excecao(cuidado(Data, IdUt, IdPrest, Descricao,Custo)) :-
    cuidado(Data, IdUt, IdPrest, Descricao, nulo1).
incerto_preco(cuidado(8,nulo1)).

utente(18, maria_de_lurdes, 68, nulo2).
excecao(utente(Id, Nome, Idade, Morada)) :-
    utente(Id, Nome, Idade, nulo2).
incerto_morada(utente(18,nulo2)).

utente(16, jose_manuel, nulo5, braga).
excecao(utente(Id, Nome, Idade, Morada)) :-
    utente(Id, Nome, nulo5, Morada).
incerto_idade(utente(16,nulo5)).

prestador(7, mario_quintas, nulo7, clipovoa, povoa_varzim).
excecao(prestador(ID, Nome, Especialidade, Instituicao, Cidade)) :- prestador(ID, Nome, nulo7, Instituicao, Cidade).
incerto_especialidade(prestador(7,nulo7)).

% Tipo II. Conhecimento Impreciso

excecao(utente(14, alfredo, 74, braga)).
excecao(utente(14, alfredo, 74, barca)).
impreciso(utente(14)).

excecao(cuidado(9,31-12-2019, 7, 6, eletrocardiograma, X)) :- X > 20, X < 30.
impreciso(cuidado(9)).


% Tipo III. Conhecimento Interdito

utente(15, renato_sancho, nulo4, moinhos).
excecao(utente(Id, Nome, Idade, Morada)) :-
    utente(Id, Nome, nulo4, Morada).
nulo(nulo4).
+utente(A,_,_,_) :: (
  solucoes(A,(utente(A,_,nulo4,_),nulo(nulo4)),B),comprimento(B,0)).

utente(17, roberto_leque, 32, nulo6).
excecao(utente(Id, Nome, Idade, Morada)) :-
    utente(Id, Nome, Idade, nulo6).
nulo(nulo6).
+utente(A,_,_,_) :: (
  solucoes(A,(utente(A,_,_,nulo6),nulo(nulo6)),B),comprimento(B,0)).

%nulo_incerto_especialidade().
%nulo_incerto_morada().
%nulo_incerto_idade().
%nulo_incerto_custo().

%impreciso_morada().
%impreciso_custo().

%nulo_interdito_prestador().
%nulo_interdito_idade().
%nulo_interdito_morada().
