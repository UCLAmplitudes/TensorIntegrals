(* ::Package:: *)

BeginPackage["TensorScalarReduction`"]

Begin["Global`"]

makeList[arg_]:=If[Head[arg]===Plus,List@@arg,{arg}];

(*Functions to find propagators, loop momenta and propagators including loop momenta from the denominator*)

findPropagators[denominator_]:=List@@denominator/.{a_^2-> a};
findLoopMomenta[propagators_]:=Cases[Flatten[makeList/@propagators]/.{-l[i_]:>l[i]},l[i_]]//DeleteDuplicates//Sort;
findNLoops[propagators_]:=Length[findLoopMomenta[propagators]];

findLoopPropagators[propagators_]:=Block[{aux,loopmomenta},
  aux={};
  loopmomenta=findLoopMomenta[propagators];
  Flatten@(If[ContainsAny[makeList[#],loopmomenta~Join~(-loopmomenta)],Append[aux,#],Nothing]&/@propagators)
];

prefactor[denominator_]:=Times@@(findLoopPropagators[findPropagators[denominator]]^2)/denominator;


(*Functions for getting T matrix and P vectors from given propagators*)

getExponent[propagators_]:=Block[{looppropagators},
  looppropagators=findLoopPropagators[propagators];
  Sum[t[i]*looppropagators[[i]]^2,{i,1,Length[looppropagators]}]//Expand
];
getTs[propagators_]:=Block[
    {exponent,loopMom},
    loopMom = findLoopMomenta[propagators];
    exponent = getExponent[propagators];
    Table[If[i===j,(Coefficient[exponent,loopMom[[i]]^2 ]),(Coefficient[exponent,loopMom[[i]]*loopMom[[j]]])/2],{i,findNLoops[propagators]},{j,findNLoops[propagators]}]
			  ];

getPs[propagators_]:=Block[
    {exponentList,loopMom},
    exponentList = makeList[getExponent[propagators]];
    loopMom = findLoopMomenta[propagators];
    Table[Plus@@(If[#==={},0,#]&/@Cases[exponentList,a__*k[j_]*loopMom[[i]]:>a *k[j]/2]),{i,findNLoops[propagators]}]
			  ];


(*Functions for dealing with tensor numerators*)

addIndex[exp_,i_]:=exp/.{k[a_]:>k[a][\[Mu][i]],l[a_]->l[a][\[Mu][i]],e[a_]->e[a][\[Mu][i]],P[a_]->P[a][\[Mu][i]]}

(*The following function builds a tensor out of a list specifying the number of each loop momenta the tensor must have*)
buildTensor[listmomenta_]:=Module[{L,aux},
  L=Length[listmomenta];
  aux=Prepend[listmomenta,0];
  Product[Times@@(l[i][\[Mu][#]]&/@Range[Sum[aux[[j]],{j,1,i}]+1,Sum[aux[[j]],{j,1,i}]+aux[[i+1]]]),{i,1,L}]
];

SetAttributes[T,Orderless];
tMatrix[nloops_]:=tMatrix[nloops]=Table[T[i,j],{i,1,nloops},{j,1,nloops}]
shifts[nloops_]:=Inverse[tMatrix[nloops]].Table[P[i],{i,1,nloops}];

shiftTensor[tensor_,nloops_]:=tensor/.{l[a_][\[Mu][i_]]:> l[a][\[Mu][i]]-addIndex[shifts[nloops][[a]],i]}//Expand;

help[list_]:=Join[{First@list},#]&/@(Rest@list)
pairings[list_List/;Length@list<3]:={{list}}
pairings[list_List/;Length@list>3]:=Module[{sublists=pairings/@(Delete[list,{{1},{#}}]&/@Range[2,Length[list]]),inter},inter=MapThread[Prepend,{sublists,({First@list,list[[#]]}&/@Range[2,Length[list]])}];
Flatten[help/@inter,1]];

prop[{a_,i_},{b_,j_},nloops_] := -1/2 \[Eta][\[Mu][i],\[Mu][j]]Inverse[tMatrix[nloops]][[a,b]]

wicks[list_,nloops_]:=Plus@@Apply[Times,pairings[list]//.{{l[a_][\[Mu][i_]],l[b_][\[Mu][j_]]}:> prop[{a,i},{b,j},nloops]},2];

integrateTensor[shiftedtensor_,nloops_]:=Block[{loopmomenta,lintegrals},
  loopmomenta=Cases[{#}/.List[c_Times]:> List@@c,l[a_][\[Mu][j_]]]&/@(List@@shiftedtensor);
  lintegrals=If[OddQ[Length[#]],0,If[Length[#]==0,1,wicks[#,nloops]]]&/@(loopmomenta);
  (List@@shiftedtensor/.{l[a_][\[Mu][i_]]->1}).lintegrals
]

findIntegrals[exp_,nloops_]:=
  (Int[Exponent[#,Flatten[tMatrix[nloops]]//DeleteDuplicates],dTest-2Exponent[#,Det[tMatrix[nloops]]]]&@exp)(exp/.{Det[tMatrix[nloops]]-> 1,T[a_,b_]->1})
  
 
findIntegralsWithP[exp_,nloops_]:=Block[{Ts,Ps,dimension},
  Ts= Map[Exponent[Numerator[exp],#]&]/@tMatrix[nloops];
  Ps=(Table[Cases[#,P[a][\[Mu][i_]]],{a,1,nloops}]&@exp)/.P[a_][\[Mu][i_]]:>i;
  dimension=dim-2(Exponent[#,Det[tMatrix[nloops]]]&)@exp; 
  Int[Ts,Ps,dimension]*(exp/.{Det[tMatrix[nloops]]-> 1,T[a_,b_]->1,P[a_][\[Mu][i_]]->1})]

rebuildNumerator[int_Int]:=Block[{num,Tpowers,Ps,dimension},
  {Tpowers,Ps,dimension}=List@@int;
  num=Times@@Union@@MapThread[Power,{tMatrix[Length[Tpowers]],Tpowers}];
  num=num*Times@@Flatten@MapThread[Thread[P[#1][#2]]&,{Range[Length[Tpowers]],Map[\[Mu]]/@Ps}];
  {num,dimension}
];

intToScalars[int_,propagators_]:=Block[{num,dimension,nts,integrals,prefactors},
{num,dimension}=rebuildNumerator[int];
num=num/.{T[a_,b_]:> getTs[propagators][[a,b]],P[a_][\[Mu][i_]]:> addIndex[getPs[propagators][[a]],i]}//Expand;
nts=Length[findLoopPropagators[propagators]];
integrals=(Int[#,dimension]&/@(1+Exponent[#,Table[t[i],{i,1,nts}]]&/@(makeList@num)));
prefactors=((makeList[num])/.{t[a_]^b_:> b!, t[a_]->1});
(integrals.prefactors)
];

intToScalars[int_,propagators_,powers_List]:=Block[
{num,dimension,nts,integrals,prefactors,toZero, zeroRep},
{num,dimension}=rebuildNumerator[int];
num=num/.{T[a_,b_]:> getTs[propagators][[a,b]],P[a_][\[Mu][i_]]:> addIndex[getPs[propagators][[a]],i]}//Expand;
nts=Length[findLoopPropagators[propagators]];
toZero = NonPositive[#]&/@powers;
zeroRep = Table[If[toZero[[i]],t[i]->0,0->0],{i,1,nts}]//Flatten;
num = num/.zeroRep;
(*nts -= Total[Boole[toZero]];*)
integrals=(Int[#,dimension]&/@(powers+Exponent[#,Table[t[i],{i,1,nts}]]&/@(makeList[num])));
prefactors=((makeList[num])/.{t[a_]^b_:> Factorial[b+powers[[a]]-1]/Factorial[powers[[a]]-1], t[a_]->1});
(integrals.prefactors)
];


tensorToScalar[propagators_,tensor_]:=Block[
{nloops,shiftedtensor,Tintegrals,loopMom,loopMomRels},
nloops=findNLoops[propagators];
loopMom = findLoopMomenta[propagators];
loopMomRels = Table[loopMom[[i]]->l[i],{i,Length[loopMom]}];
shiftedtensor=shiftTensor[tensor/.loopMomRels,nloops];
firstint=integrateTensor[shiftedtensor,nloops];
Tintegrals=Total[findIntegralsWithP[#,nloops]&/@makeList[integrateTensor[shiftedtensor,nloops]]];
(*Print[Tintegrals];*)
Tintegrals/.{Int[a__]:> intToScalars[Int[a],propagators/.loopMomRels]}
];

tensorToScalar[propagators_,tensor_,powers_List]:=Block[
{nloops,shiftedtensor,Tintegrals,loopMom,loopMomRels},
nloops=findNLoops[propagators];
loopMom = findLoopMomenta[propagators];
loopMomRels = Table[loopMom[[i]]->l[i],{i,Length[loopMom]}];
shiftedtensor=shiftTensor[tensor/.loopMomRels,nloops];
firstint=integrateTensor[shiftedtensor,nloops];
Tintegrals=Total[findIntegralsWithP[#,nloops]&/@makeList[integrateTensor[shiftedtensor,nloops]]];
(*Print[Tintegrals];*)
Tintegrals/.{Int[a__]:> intToScalars[Int[a],propagators/.loopMomRels,powers]}
];


letterIndices[list_]:=Block[{ordering},
ordering=list//Flatten;
list/.Table[ordering[[i]]-> ToExpression[Alphabet[][[i]]],{i,Length[ordering]}]
];
canonicalOrder[list_]:=Block[{ordering},
ordering=list//Flatten;
list/.Table[ordering[[i]]-> (ordering//Sort)[[i]],{i,Length[ordering]}]
];
canonicalSequentialOrder[list_]:=Block[{ordering},
ordering=list//Flatten;
list/.Table[ordering[[i]]-> Range[Length[ordering]][[i]],{i,Length[ordering]}]
];
fromCanonicalSequentialOrder[list_]:=Block[{ordering},
ordering=list//Flatten;
Table[ \[Mu][Range[Length[ordering]][[i]]]->\[Mu][ordering[[i]]],{i,Length[ordering]}]
];


End[ ]

EndPackage[ ]
