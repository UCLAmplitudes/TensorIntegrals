(* ::Package:: *)

BeginPackage["TensorScalarReduction`"]

Begin["Global`"]

(*Functions to find propagators, loop momenta and propagators including loop momenta from the denominator*)

FindPropagators[denominator_]:=List@@denominator/.{a_^2-> a};
FindLoopMomenta[propagators_]:=Cases[Flatten[MakeList/@propagators]/.{-l[i_]:>l[i]},l[i_]]//DeleteDuplicates//Sort;
FindNLoops[propagators_]:=Length[FindLoopMomenta[propagators]];

MakeList[arg_]:=If[Head[arg]===Plus,List@@arg,{arg}];

FindLoopPropagators[propagators_]:=Block[{aux,loopmomenta},
  aux={};
  loopmomenta=FindLoopMomenta[propagators];
  Flatten@(If[ContainsAny[MakeList[#],loopmomenta~Join~(-loopmomenta)],Append[aux,#],Nothing]&/@propagators)
];

Prefactor[denominator_]:=Times@@(FindLoopPropagators[FindPropagators[denominator]]^2)/denominator;


(*Functions for getting T matrix and P vectors from given propagators*)

GetExponent[propagators_]:=Block[{looppropagators},
  looppropagators=FindLoopPropagators[propagators];
  Sum[t[i]*looppropagators[[i]]^2,{i,1,Length[looppropagators]}]//Expand
];
GetTs[propagators_]:=Block[
    {exponent,loopMom},
    loopMom = FindLoopMomenta[propagators];
    exponent = GetExponent[propagators];
    Table[If[i===j,(Coefficient[exponent,loopMom[[i]]^2 ]),(Coefficient[exponent,loopMom[[i]]*loopMom[[j]]])/2],{i,FindNLoops[propagators]},{j,FindNLoops[propagators]}]
			  ];

GetPs[propagators_]:=Block[
    {exponentList,loopMom},
    exponentList = MakeList[GetExponent[propagators]];
    loopMom = FindLoopMomenta[propagators];
    Table[Plus@@(If[#==={},0,#]&/@Cases[exponentList,a__*k[j_]*loopMom[[i]]:>a *k[j]/2]),{i,FindNLoops[propagators]}]
			  ];


(*Functions for dealing with tensor numerators*)

AddIndex[exp_,i_]:=exp/.{k[a_]:>k[a][\[Mu][i]],l[a_]->l[a][\[Mu][i]],e[a_]->e[a][\[Mu][i]],P[a_]->P[a][\[Mu][i]]}

(*The following function builds a tensor out of a list specifying the number of each loop momenta the tensor must have*)
BuildTensor[listmomenta_]:=Module[{L,aux},
  L=Length[listmomenta];
  aux=Prepend[listmomenta,0];
  Product[Times@@(l[i][\[Mu][#]]&/@Range[Sum[aux[[j]],{j,1,i}]+1,Sum[aux[[j]],{j,1,i}]+aux[[i+1]]]),{i,1,L}]
];

SetAttributes[T,Orderless];
TMatrix[nloops_]:=TMatrix[nloops]=Table[T[i,j],{i,1,nloops},{j,1,nloops}]
Shifts[nloops_]:=Inverse[TMatrix[nloops]].Table[P[i],{i,1,nloops}];

ShiftTensor[tensor_,nloops_]:=tensor/.{l[a_][\[Mu][i_]]:> l[a][\[Mu][i]]-AddIndex[Shifts[nloops][[a]],i]}//Expand;

help[list_]:=Join[{First@list},#]&/@(Rest@list)
Pairings[list_List/;Length@list<3]:={{list}}
Pairings[list_List/;Length@list>3]:=Module[{sublists=Pairings/@(Delete[list,{{1},{#}}]&/@Range[2,Length[list]]),inter},inter=MapThread[Prepend,{sublists,({First@list,list[[#]]}&/@Range[2,Length[list]])}];
Flatten[help/@inter,1]];

Prop[{a_,i_},{b_,j_},nloops_] := -1/2 \[Eta][\[Mu][i],\[Mu][j]]Inverse[TMatrix[nloops]][[a,b]]

Wicks[list_,nloops_]:=Plus@@Apply[Times,Pairings[list]//.{{l[a_][\[Mu][i_]],l[b_][\[Mu][j_]]}:> Prop[{a,i},{b,j},nloops]},2];

IntegrateTensor[shiftedtensor_,nloops_]:=Block[{loopmomenta,lintegrals},
  loopmomenta=Cases[{#}/.List[c_Times]:> List@@c,l[a_][\[Mu][j_]]]&/@(List@@shiftedtensor);
  lintegrals=If[OddQ[Length[#]],0,If[Length[#]==0,1,Wicks[#,nloops]]]&/@(loopmomenta);
  (List@@shiftedtensor/.{l[a_][\[Mu][i_]]->1}).lintegrals
]

FindIntegrals[exp_,nloops_]:=
  (Int[Exponent[#,Flatten[TMatrix[nloops]]//DeleteDuplicates],dTest-2Exponent[#,Det[TMatrix[nloops]]]]&@exp)(exp/.{Det[TMatrix[nloops]]-> 1,T[a_,b_]->1})

FindIntegralsWithP[exp_,nloops_]:=Block[{Ts,Ps,dimension},
  Ts= (Exponent[Numerator[#],Flatten[TMatrix[nloops]]//DeleteDuplicates]&)@exp;
  Ps=(Table[Cases[#,P[a][\[Mu][i_]]],{a,1,nloops}]&@exp)/.P[a_][\[Mu][i_]]:>i;
  dimension=dim-2(Exponent[#,Det[TMatrix[nloops]]]&)@exp; 
  (Int@{Ts,Ps,dimension})*(exp/.{Det[TMatrix[nloops]]-> 1,T[a_,b_]->1,P[a_][\[Mu][i_]]->1})]

SetAttributes[FindIntegralsWithPList,HoldAll]
FindIntegralsWithPList[exp_,nloops_,listints_]:=Block[{Ts,Ps,dimension,res},
  Ts= (Exponent[#,Flatten[TMatrix[nloops]]//DeleteDuplicates]&)@exp;
  Ps=(Table[Cases[#,P[a][\[Mu][i_]]],{a,1,nloops}]&@exp)/.P[a_][\[Mu][i_]]:>i;
  dimension=dim-2(Exponent[#,Det[TMatrix[nloops]]]&)@exp; 
  res=Reap[Sow[Int@{Ts,Ps,dimension}]*(exp/.{Det[TMatrix[nloops]]-> 1,T[a_,b_]->1,P[a_][\[Mu][i_]]->1})];
  listints=Append[listints,res[[2]]];
  Return[res[[1]]];
];

RebuildNumerator[int_]:=Block[{num,Tpowers,Ps,dimension},
  {Tpowers,Ps,dimension}=int/.Int[a__]-> a;
  num=Times@@Power[#1,#2]&[(Flatten[TMatrix[1]]//DeleteDuplicates),Tpowers];
  For[i=1,i<= Length[Ps],i++,
    num=num*Times@@(P[i][\[Mu][#]]&/@Ps[[i]]);
  ];
  {num,dimension}
];

IntToScalars[int_,propagators_]:=Block[{num,dimension,nts,integrals,prefactors},
{num,dimension}=RebuildNumerator[int];
num=num/.{T[a_,b_]:> GetTs[propagators][[a,b]],P[a_][\[Mu][i_]]:> AddIndex[GetPs[propagators][[a]],i]}//Expand;
nts=Length[FindLoopPropagators[propagators]];
integrals=(Int[#,dimension]&/@(1+Exponent[#,Table[t[i],{i,1,nts}]]&/@(MakeList@num)));
prefactors=((MakeList[num])/.{t[a_]^b_:> b!, t[a_]->1});
(integrals.prefactors)
];

IntToScalars[int_,propagators_,powers_List]:=Block[
{num,dimension,nts,integrals,prefactors,toZero, zeroRep},
{num,dimension}=RebuildNumerator[int];
num=num/.{T[a_,b_]:> GetTs[propagators][[a,b]],P[a_][\[Mu][i_]]:> AddIndex[GetPs[propagators][[a]],i]}//Expand;
nts=Length[FindLoopPropagators[propagators]];
toZero = NonPositive[#]&/@powers;
zeroRep = Table[If[toZero[[i]],t[i]->0,0->0],{i,1,nts}]//Flatten;
num = num/.zeroRep;
(*nts -= Total[Boole[toZero]];*)
integrals=(Int[#,dimension]&/@(powers+Exponent[#,Table[t[i],{i,1,nts}]]&/@(MakeList[num])));
prefactors=((MakeList[num])/.{t[a_]^b_:> Factorial[b+powers[[a]]-1]/Factorial[powers[[a]]-1], t[a_]->1});
(integrals.prefactors)
];

SetAttributes[IntToScalarsList,HoldAll]
IntToScalarsList[int_,propagators_,listints_]:=Block[{num,dimension,nts,res},
{num,dimension}=RebuildNumerator[int];
num=num/.{T[a_,b_]:> GetTs[propagators][[a,b]],P[a_][\[Mu][i_]]:> AddIndex[GetPs[propagators][[a]],i]}//Expand;
nts=Length[FindLoopPropagators@propagators];
res=Reap[(-1)^nts*(Sow[Int[#,dimension]]&/@(1+Exponent[#,Table[t[i],{i,1,nts}]]&/@MakeList[num])).(MakeList[num]/.{t[a_]^b_-> (-1)^b b!,t[a_]->-1})];
listints=Append[listints,res[[2]]];
Return[res[[1]]];
];

TensorToScalar[propagators_,tensor_]:=Block[
{nloops,shiftedtensor,Tintegrals,loopMom,loopMomRels},
nloops=FindNLoops[propagators];
loopMom = FindLoopMomenta[propagators];
loopMomRels = Table[loopMom[[i]]->l[i],{i,Length[loopMom]}];
shiftedtensor=ShiftTensor[tensor/.loopMomRels,nloops];
firstint=IntegrateTensor[shiftedtensor,nloops];
Tintegrals=Total[FindIntegralsWithP[#,nloops]&/@MakeList[IntegrateTensor[shiftedtensor,nloops]]];
(*Print[Tintegrals];*)
Tintegrals/.{Int[a__]:> IntToScalars[Int[a],propagators/.loopMomRels]}
];

TensorToScalar[propagators_,tensor_,powers_List]:=Block[
{nloops,shiftedtensor,Tintegrals,loopMom,loopMomRels},
nloops=FindNLoops[propagators];
loopMom = FindLoopMomenta[propagators];
loopMomRels = Table[loopMom[[i]]->l[i],{i,Length[loopMom]}];
shiftedtensor=ShiftTensor[tensor/.loopMomRels,nloops];
firstint=IntegrateTensor[shiftedtensor,nloops];
Tintegrals=Total[FindIntegralsWithP[#,nloops]&/@MakeList[IntegrateTensor[shiftedtensor,nloops]]];
(*Print[Tintegrals];*)
Tintegrals/.{Int[a__]:> IntToScalars[Int[a],propagators/.loopMomRels,powers]}
];


LetterIndices[list_]:=Block[{ordering},
ordering=list//Flatten;
list/.Table[ordering[[i]]-> ToExpression[Alphabet[][[i]]],{i,Length[ordering]}]
];
CanonicalOrder[list_]:=Block[{ordering},
ordering=list//Flatten;
list/.Table[ordering[[i]]-> (ordering//Sort)[[i]],{i,Length[ordering]}]
];
CanonicalSequentialOrder[list_]:=Block[{ordering},
ordering=list//Flatten;
list/.Table[ordering[[i]]-> Range[Length[ordering]][[i]],{i,Length[ordering]}]
];
FromCanonicalSequentialOrder[list_]:=Block[{ordering},
ordering=list//Flatten;
Table[ \[Mu][Range[Length[ordering]][[i]]]->\[Mu][ordering[[i]]],{i,Length[ordering]}]
];


End[ ]

EndPackage[ ]
