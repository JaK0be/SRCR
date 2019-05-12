%--------------------------------- - - - - - - - - - -  -  -  -  -   -
% SIST. REPR. CONHECIMENTO E RACIOCINIO - MiEI/3

%--------------------------------- - - - - - - - - - -  -  -  -  -   -
% Base de Conhecimento com informacao genealogica.

%--------------------------------- - - - - - - - - - -  -  -  -  -   -
% SICStus PROLOG: Declaracoes iniciais

:- set_prolog_flag( discontiguous_warnings,off ).
:- set_prolog_flag( single_var_warnings,off ).
:- set_prolog_flag( unknown,fail ).


% Definições iniciais
:- op(900,xfy,'::').
:- dynamic utente/4.
:- dynamic servico/4.
:- dynamic consulta/4.
:- dynamic sexo/2.



%--------------------------------- - - - - - - - - - -  -  -  -  -   -

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

% utente: #IdUt, Nome, Idade, Morada -> { V, F }
utente(1,joao_pimentel,20,esposende).
utente(2,bruno_veloso,22,ponte_da_barca).
utente(3,jaime_leite,20,felgueiras).
utente(4,pedro_goncalves,20,felgueiras).
utente(5,rodolfo_silva,20,trofa).
utente(6,joana_amorim,22,viana_do_castelo).
utente(7,gloria_borga,53,portimao).
utente(8,andreia_silva,27,trofa).


% serviço: #IdServ, Descrição, Instituição, Cidade -> { V, F }
servico(1,medicina_geral,trofa_saude,braga).
servico(2,cardiologia,cufe,porto).
servico(3,oftalmologia,sao_joao,porto).
servico(4,otorrinolarengologia,particular,viana).
servico(5,ginecologia,trofa_saude,braga).
servico(6,cirurgia_geral,santo_antonio,porto).


% consulta: Data, #IdUt, #IdServ, Custo  -> { V, F }
consulta(2019-03-06,1,1,14).
consulta(2014-04-06,1,3,22).
consulta(2014-03-07,3,5,32).
consulta(2019-05-12,5,2,9).
consulta(2019-02-26,2,5,10).
consulta(2019-12-29,3,2,15).
consulta(2019-3-7, 1, 1, 20).

% --------------------------------------------------------------------------
% Registar utentes, serviços e consultas;
adiciona(T) :- solucoes(Inv, +T::Inv, S),
               insere(T),
               testa(S).

insere(T) :- assert(T).
insere(T) :- retract(T),!,fail.

testa([]).
testa([H|T]) :- H, testa(T).

% --------------------------------------------------------------------------
% Invariante Estrutural:  nao permitir a insercao de conhecimento repetido

+utente(Id,Nome,Idade,Cidade ) :: (solucoes( (Id,Nome,Idade,Cidade),(utente( Id,Nome,Idade,Cidade )),S ),
                  comprimento( S,N ), N == 1
                  ).

+servico(Id,Descricao,Instituicao,Cidade ) :: (solucoes( (Id,Descricao,Instituicao,Cidade),(servico( Id,Descricao,Instituicao,Cidade )),S ),
                  comprimento( S,N ), N == 1
                  ).


% --------------------------------------------------------------------------
% Invariante Referencial : não permitir a inserção de utentes/servicos com o mesmo ID

+utente(Id,_,_,_) :: (solucoes( (Id,Nome,Idade,Local), (utente(Id,Nome,Idade,Local)),S ),
                                 comprimento( S,N ),
				                 N==1).


+servico(Id,_,_,_) :: (solucoes( (Id,Descricao,Instituicao,Cidade), (servico(Id,Descricao,Instituicao,Cidade)),S ),
                                 comprimento( S,N ),
				                 N==1).


% --------------------------------------------------------------------------
% Invariante Referencial : não permitir a inserção de servicos duplicados na mesma instituicao e local
+servico(_,Descricao,Instituicao,Cidade) :: (solucoes( (Id,Descricao,Instituicao,Cidade), (servico(Id,Descricao,Instituicao,Cidade)),S ),
                                 comprimento( S,N ),
				                 N==1).



% Invariante Referencial: garantir que utente/servico existe antes de marcar consulta
+consulta(_,IdUt,_,_) :: (solucoes( (IdUt), (utente(IdUt,Nome,Idade,Local)),S ),
                                 comprimento( S,N ),
				                 N==1).

+consulta(_,_,IdServ,_) :: (solucoes( (IdServ), (servico(IdServ,Descricao,Instituicao,Cidade)),S ),
                                 comprimento( S,N ),
				                 N==1).


% --------------------------------------------------------------------------
% Remover utentes, serviços e consultas;

remove(T) :- solucoes(I,-T::I,S),
              apagar(T),
              testa(S).

apagar(T) :- retract(T).
apagar(T) :- assert(T),!,fail.


% Invariante Referencial:  não permitir a remoção de utentes/serviços que têm uma consulta associada

-utente(IdUt,_,_,_) :: (solucoes( (IdUt),(consulta(_,IdUt,_,_)),S ),
                                  comprimento( S,N ),
				                  N==0).

-servico(IdServ,Nome,Especialidade,Local) :: (solucoes( (IdServ,Nome,Especialidade,Local), consulta(_,_,IdServ,_),S ),
                                                comprimento( S,N ),
				                                N==0).


% --------------------------------------------------------------------------
% Identificar as instituições prestadoras de serviços;

% Predicado unicos:
% Lista1, Lista2 -> {V,F}
unicos([],[]).
unicos([H|T], R) :-
	pertence(H,T),
	unicos(T,R).
unicos([H|T], [H|R]) :-
	\+ (pertence(H,T)),
	unicos(T,R).

% Predicado instituicoes:
% Lista -> {V,F}
instituicoes(S):-
    solucoes(I, servico(_,_,I,_), L),
    sort(L,S).

% Predicado servicos:
% Lista -> {V,F}
servicos(S):-
    solucoes(D, servico(_,D,_,_), L),
    sort(L,S).


% --------------------------------------------------------------------------
% Identificar utentes/serviços/consultas por critérios de seleção;

% Predicado identificar_utente_por_Id:
% Id, Lista de Utentes -> {V,F}
identificar_utente_por_id(Id,S):-
  solucoes(
          (Nome,Idade,Local),
          (utente(Id,Nome,Idade,Local)),
          S
          ).

% Predicado identificar_utente_por_Nome:
% nome, Lista de Utentes -> {V,F}
identificar_utente_por_nome(Nome,S):-
  solucoes(
          (Id,Idade,Local),
          (utente(Id,Nome,Idade,Local)),
          S
          ).

% Predicado identificar_utente_por_Idade:
% Idade, Lista de Utentes -> {V,F}
identificar_utente_por_idade(Idade,S):-
  solucoes(
          (Id,Nome,Local),
          (utente(Id,Nome,Idade,Local)),
          S
          ).

% Predicado identificar_utente_por_Local:
% Local, Lista de Utentes -> {V,F}
identificar_utente_por_local(Local,S):-
  solucoes(
          (Id,Nome,Idade),
          (utente(Id,Nome,Idade,Local)),
          S
          ).

% -----------------------------------------

% Predicado identificar_servico_por_Id:
% Id, Lista de Servicos -> {V,F}
identificar_servico_por_id(Id,S):-
  solucoes(
          (Descricao,Instituicao,Cidade),
          (servico(Id,Descricao,Instituicao,Cidade)),
          S
          ).

% Predicado identificar_servico_por_Descricao:
% Descricao, Lista de Servicos -> {V,F}
identificar_servico_por_descricao(Descricao,S):-
  solucoes(
          (Id,Instituicao,Cidade),
          (servico(Id,Descricao,Instituicao,Cidade)),
          S
          ).

% Predicado identificar_servico_por_Instituicao:
% Instituicao, Lista de Servicos -> {V,F}
identificar_servico_por_instituicao(Instituicao,S):-
  solucoes(
          (Id,Descricao,Cidade),
          (servico(Id,Descricao,Instituicao,Cidade)),
          S
          ).

% Predicado identificar_servico_por_Cidade:
% Cidade, Lista de Servicos -> {V,F}
identificar_servico_por_cidade(Cidade,S):-
  solucoes(
          (Id,Descricao,Instituicao),
          (servico(Id,Descricao,Instituicao,Cidade)),
          S
          ).


% -----------------------------------------

% Predicado identificar_consulta_por_Utente:
% Id, Lista de Consultas -> {V,F}
identificar_consulta_por_utente(IdUt,S):-
  solucoes(
          (Data,IdServ,Custo),
          (consulta(Data,IdUt,IdServ,Custo)),
          S
          ).

% Predicado identificar_consulta_por_Servico:
% Id, Lista de Consultas -> {V,F}
identificar_consulta_por_servico(IdServ,S):-
  solucoes(
          (Data,IdUt,Custo),
          (consulta(Data,IdUt,IdServ,Custo)),
          S
          ).

% Predicado identificar_consulta_por_Data:
% Data, Lista de Consultas -> {V,F}
identificar_consulta_por_data(Data,S):-
  solucoes(
          (IdUt,IdServ,Custo),
          (consulta(Data,IdUt,IdServ,Custo)),
          S
          ).

% Predicado identificar_consulta_por_Custo:
% Custo, Lista de Consultas -> {V,F}
identificar_consulta_por_custo(Custo,S):-
  solucoes(
          (Data,IdUt,IdServ),
          (consulta(Data,IdUt,IdServ,Custo)),
          S
          ).


% --------------------------------------------------------------------------
% Identificar serviços prestados por instituição/cidade/datas/custo;

% Predicado servicos_por_instituicao:
% Instituicao, Lista de Servicos -> {V,F}
servicos_por_instituicao(Instituicao,S) :-
	solucoes(
			(Descricao,Cidade),
			(
				servico(IdServ,Descricao,Instituicao,Cidade)
			),
			S
		).

% Predicado servicos_por_cidade:
% Cidade, Lista de Servicos -> {V,F}
servicos_por_cidade(Cidade,S) :-
	solucoes(
			(Descricao,Instituicao),
			(
				servico(IdServ,Descricao,Instituicao,Cidade)
			),
			S
		).

% Predicado consultas_por_instituicao:
% Instituicao, Lista de Consultas -> {V,F}
consultas_por_instituicao(Instituicao,S) :-
	solucoes(
			(Data,IdUt,IdServ,Preco,Descricao),
			(
				consulta(Data,IdUt,IdServ,Preco),
				servico(IdServ,Descricao,Instituicao,_)
			),
			S
		).

% Predicado consultas_por_cidade:
% Cidade, Lista de Consultas -> {V,F}
consultas_por_cidade(Cidade,S) :-
	solucoes(
			(Data,IdUt,IdServ,Preco,Descricao),
			(
				consulta(Data,IdUt,IdServ,Preco),
				servico(IdServ,Descricao,Instituicao,Cidade)
			),
			S
		).

% Predicado consultas_por_data:
% Data, Lista de Consultas -> {V,F}
consultas_por_data(Data,S) :-
	solucoes(
			(IdUt,IdServ,Preco,Descricao),
			(
				consulta(Data,IdUt,IdServ,Preco),
				servico(IdServ,Descricao,Instituicao,Cidade)
			),
			S
		).

% Predicado consultas_por_preco:
% Preco, Lista de Consultas -> {V,F}
consultas_por_preco(Preco,S) :-
	solucoes(
			(Data,IdUt,IdServ,Descricao),
			(
				consulta(Data,IdUt,IdServ,Preco),
				servico(IdServ,Descricao,Instituicao,Cidade)
			),
			S
		).

% Predicado consultas_por_intervalo:
% Data, Data, Lista de Consultas -> {V,F}
consultas_por_intervalo(DataInicio,DataFim,L) :- 
	solucoes(
			(Data, IdUt, IdServ, Custo),
			(
				consulta(Data, IdUt, IdServ, Custo), 
				compDate(Data,DataInicio), 
				compDate(DataFim,Data)
			),
			L
		).


% --------------------------------------------------------------------------
% Identificar os utentes de um serviço/instituição;

% Predicado utentes_de_servico:
% Servico, Lista de Utentes -> {V,F}
utentes_de_servico(IdServ,S) :-
	solucoes(
			(IdUt,Nome),
			(
				utente(IdUt,Nome,Idade,Local),
				servico(IdServ,_,_,_),
				consulta(_,IdUt,IdServ,_)
			),
			L
		),
	sort(L,S).

% Predicado utentes_de_instituicao:
% Instituicao, Lista de Utentes -> {V,F}
utentes_de_instituicao(Instituicao,S) :-
	solucoes(
			(IdUt,Nome),
			(
				utente(IdUt,Nome,Idade,Local),
				servico(IdServ,_,Instituicao,_),
				consulta(_,IdUt,IdServ,_)
			),
			L
		),
	sort(L,S).




% --------------------------------------------------------------------------
% Identificar serviços realizados por utente/instituição/cidade;

% Predicado servicos_realizados_por_utente:
% Utente, Lista de Servico -> {V,F}
servicos_realizados_por_utente(IdUt,S) :-
	solucoes(
			(Data,Descricao,Preco),
			(
				utente(IdUt,Nome,Idade,Local),
				servico(IdServ,Descricao,Instituicao,Cidade),
				consulta(Data,IdUt,IdServ,Preco)
			),
			S
		).

% Predicado servicos_realizados_por_instituicao:
% Instituicao, Lista de Servico -> {V,F}
servicos_realizados_por_instituicao(Instituicao,S) :-
	solucoes(
			(Data,Descricao,Preco,Cidade),
			(
				utente(IdUt,Nome,Idade,Local),
				servico(IdServ,Descricao,Instituicao,Cidade),
				consulta(Data,IdUt,IdServ,Preco)
			),
			S
		).

% Predicado servicos_realizados_por_cidade:
% Cidade, Lista de Servico -> {V,F}
servicos_realizados_por_cidade(Cidade,S) :-
	solucoes(
			(Data,Descricao,Preco,Instituicao),
			(
				utente(IdUt,Nome,Idade,Local),
				servico(IdServ,Descricao,Instituicao,Cidade),
				consulta(Data,IdUt,IdServ,Preco)
			),
			S
		).


% --------------------------------------------------------------------------
% Calcular o custo total dos cuidados de saúde por utente/serviço/instituição/data.

% Extensão do predicado soma: 
% Lista, Valor -> {V, F}
soma([], 0).
soma([X|L], R) :- soma(L, R1), R is X + R1.

% Predicado custo_por_utente:
% Utente, Valor -> {V,F}
custo_por_utente(IdUt,S) :-
	solucoes(
			(Preco),
			(
				utente(IdUt,_,_,_),
				consulta(_,IdUt,_,Preco)
			),
			L
		),
	soma(L,S).

% Predicado custo_por_servico:
% Servico, Valor -> {V,F}
custo_por_servico(IdServ,S) :-
	solucoes(
			(Preco),
			(
				servico(IdServ,_,_,_),
				consulta(_,_,IdServ,Preco)
			),
			L
		),
	soma(L,S).

% Predicado custo_por_instituicao:
% Instituicao, Valor -> {V,F}
custo_por_instituicao(Instituicao,S) :-
	solucoes(
			(Preco),
			(
				servico(IdServ,_,Instituicao,_),
				consulta(_,_,IdServ,Preco)
			),
			L
		),
	soma(L,S).

% Predicado custo_por_data:
% Data, Valor -> {V,F}
custo_por_data(Data,S) :-
	solucoes(
			(Preco),
			(
				consulta(Data,_,_,Preco)
			),
			L
		),
	soma(L,S).


%------------------------------------------------------------------------------------------------------------------------------------------------
 
% Extensão do predicado comparaDate: (Y1,M1,D1), (Y2,M2,D2) -> {V,F}
% Compara 2 datas assumindo que estas sao representadas por 1 triplo.
compDate(Y1-M1-D1,Y2-M2-D2) :- Y1 > Y2.
compDate(Y-M1-D1,Y-M2-D2) :- M1 > M2.
compDate(Y-M-D1,Y-M-D2) :- D1 >= D2.

% Predicado custo_por_intervalo:
% Data, Data, Valor -> {V,F}
custo_por_intervalo(DataInicio,DataFim,C) :- 
	solucoes(
			Preco,
			(
				consulta(X,_,_,Preco), 
				compDate(X,DataInicio), 
				compDate(DataFim,X)
			),
			L
		), 
	soma(L,C).


%------------------------------------------------------------------------------------------------------------------------------------------------
% EXTRAS:
%------------------------------------------------------------------------------------------------------------------------------------------------
% Predicado sexo: IdUt, Sexo -> {V,F}
sexo(1,m).
sexo(2,m).
sexo(3,m).
sexo(4,m).
sexo(5,m).
sexo(6,f).
sexo(7,f).
sexo(8,f).

% --------------------------------------------------------------------------
% Invariante Estrutural:  nao permitir a insercao de conhecimento repetido
+sexo(IdUt,Valor) :: (solucoes( (IdUt,Valor), (sexo(IdUt,Valor)),S ),
                                 comprimento( S,N ),
				                 N==1).

% --------------------------------------------------------------------------
% Invariante Referencial : não permitir a inserção de informacao sobre o genero de um utente que nao existe
+sexo(IdUt,_) :: (solucoes( (IdUt), (utente(IdUt,_,_,_)),S ),
                                 comprimento( S,N ),
				                 N==1).

% --------------------------------------------------------------------------
% Invariante Referencial : não permitir a inserção de informacao sobre o genero de um utente que nao seja valida
+sexo(IdUt,Valor) :: valida_sexo(Valor).

%Predicado valida_sexo:
%genero -> {V,F}
valida_sexo(m).
valida_sexo(f).

% --------------------------------------------------------------------------
% Invariante Referencial : não permitir a remoção de um utente que possua informação sobre o seu genero
-utente(IdUt,_,_,_) :: (solucoes( (IdUt),(sexo(IdUt,_)),S ),
                                  comprimento( S,N ),
				                  N==0).


% ------------------------------------------------------
% Verificar o serviço mais prestado por um prestador:

%Predicado preco_medio_de_servico:
%ID do servico, media dos precos -> {V,F}
preco_medio_de_servico(IdServ,M):-
    solucoes(
    	P,
    	(
    		consulta(_,_,IdServ,P)
    	),
    	S
    ),
    media(S,M).

% ------------------------------------------------------
% Verificar o valor total gasto consoante o genero do utente:

%Predicado valor_gasto_por_genero:
%Genero, Valor -> {V,F}
valor_gasto_por_genero(G,V) :-
	solucoes(
		Preco,
		(
			sexo(IdUt,G),
			consulta(_,IdUt,_,Preco)
			),
		S),
	soma(S,V).

% Predicado media:
% Lista, Valor -> {V,F}
media([],0).
media(List,Med) :-
    soma(List,X),
    comprimento(List,L),
    Med is (div(X,L)).

% ------------------------------------------------------
% Verificar a idade media dos utentes de um servico:

% Predicado idade_media_por_servico:
% servico, Idade media -> {V,F}
idade_media_por_servico(Desc,Valor) :-
    solucoes(
        Idade,
        (
            utente(IdUt,_,Idade,_),
            servico(IdServ,Desc,_,_),
            consulta(_,IdUt,IdServ,_)
        ),
        S),
    media(S,Valor).

% ------------------------------------------------------
% Verificar a idade media dos utentes de uma instituicao:

% Predicado idade_media_por_instituicao:
% instituicao, Idade media -> {V,F}
idade_media_por_instituicao(Inst,Valor) :-
    solucoes(
        Idade,
        (
            utente(IdUt,_,Idade,_),
            servico(IdServ,_,Inst,_),
            consulta(_,IdUt,IdServ,_)
        ),
        S),
    media(S,Valor).
