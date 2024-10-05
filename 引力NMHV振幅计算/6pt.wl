(* ::Package:: *)

Off[Solve::svars]
SetDirectory[NotebookDirectory[]]
Get[FindFile["SpinorHelicity4D`"]]
<<tree_amplitudes.m


(*\:51fd\:6570\:5b9a\:4e49\:ff0c\:4e3b\:8981\:7528\:6765\:6c42\:89e3\:88ab\:79ef\:51fd\:6570*)
n=6;
k=3;
u=1;
v=2;
r=k+1;
sss=k+2;
cm=Table[Subscript[c, i,j],{i,k},{j,n}];
Subscript[c, i_,j_]:=0/;j<=k&&i<j
Subscript[c, i_,i_]:=1;
Subscript[c, i_,j_]:=Subscript[c, j,i]/;i>j
Gr=DeleteCases[Flatten[cm],_Integer];
gm[i_,j_,k_]:=Transpose[{cm[[All,i]],cm[[All,j]],cm[[All,k]]}];
cd[i_,j_,k_,l_]:=Subscript[c, i,k] Subscript[c, j,l]-Subscript[c, i,l] Subscript[c, j,k];
DD[a_,b_,cc_,d_]:={{Subscript[c, a,cc],Subscript[c, a,d]},{Subscript[c, b,cc],Subscript[c, b,d]}};
H[a_,b_,cc_,d_]:=Det[DD[a,b,cc,d]]/Product[Flatten[DD[a,b,cc,d]][[i]],{i,4}];
Subscript[w1, i_,j_]:=SpinorAngleBracket[i,j]/H[i,j,r,sss];
Subscript[w2, A_,B_]:=SpinorSquareBracket[A,B]/H[A,B,u,v];
cyc[i_,I_]:=If [Mod[i,Length[I]]===0,Length[I],Mod[i,Length[I]]];
V[up_,down_]:=Table[Table[Subscript[c, down[[i]],up[[cyc[j,up]]]] Subscript[c, down[[i]],up[[cyc[j+1,up]]]],{j,Length[up]}],{i,Length[down]}];
J[S_,W_]:=FullSimplify[Product[Subscript[w1, S[[i,1]],S[[i,2]]],{i,Length[S]}]Product[Subscript[w2, W[[i,1]],W[[i,2]]],{i,Length[W]}]Det[DD[u,v,r,sss]]^(1+(k-2)(n-k-2))/(Product[Flatten[DD[u,v,r,sss]][[i]],{i,4}]^2*Product[Gr[[i]],{i,Length[Gr]}])];
Ctilde=Table[Det[V[{a,u,v},{r,sss,B}]],{a,Complement[Range[k],{u,v}]},{B,Complement[Range[k+1,n],{r,sss}]}]//Flatten;
Ct=Product[Ctilde[[i]],{i,Length[Ctilde]}];
Jtrees={J[{{1,2},{2,3}},{{4,5},{5,6}}]}
tau=Table[Subscript[\[Tau], i],{i,k+1,n}];
myperm[expr_,l__,list__]:=Module[{return=expr,var=Variables@expr},return/. Table[var[[i]]->(var[[i]]/. Table[l[[b]]->list[[b]],{b,1,Length@l}]),{i,1,Length@var}]];


(*\:5f00\:59cb\:6c42\:89e3\:7559\:6570*)
Sol1=Flatten[Table[{Subscript[c, i,1]-> (SpinorAngleBracket[i,3]-SpinorAngleBracket[2,3] Subscript[\[Tau], i])/SpinorAngleBracket[1,3],Subscript[c, i,2]-> Subscript[\[Tau], i],Subscript[c, i,3]-> -(SpinorAngleBracket[i,1]-SpinorAngleBracket[2,1] Subscript[\[Tau], i])/SpinorAngleBracket[1,3]},{i,k+1,n}]];
JtreesSolution={};
ctreesSolution={};
For[q=1,q<=Length[Jtrees],q++,
	Print["\:73b0\:5728\:8ba1\:7b97\:7b2c"<>ToString[q]<>"\:68f5\:6570"];
	cSolution={};
	JSolution={};
	poles=DeleteCases[DeleteCases[Flatten[FactorList[Denominator[Jtrees[[q]]]]],1],-1];
	For[i=1,i<=Length[poles],i++,
		pole={poles[[i]]};
		PolesProduct=Product[pole[[i]],{i,Length[pole]}];
		Print["\:5f53\:524d\:6c42\:89e3:"<>ToString[pole,TraditionalForm]];
		Eq=pole/.Sol1;
		Sol2=Solve[Eq==0,tau][[1]];
		index=Table[Sol2[[i]][[1]][[2]],{i,Length[Sol2]}];
		indexbar=Complement[Range[k+1,n],index];
		Eqtau1=Table[Sol2[[i]][[1]]-Sol2[[i]][[2]],{i,Length[Sol2]}];
		Eq2=Table[SpinorSquareBracket[2,i]+Sum[Subscript[\[Tau], j]SpinorSquareBracket[j,i],{j,Range[k+1,n]}],{i,indexbar}];
		Sol3=Together[SchoutenSimplify[Solve[{Eq2==0,Eqtau1==0},tau]]][[1]];
		Solc=Together[Sol1/.Sol3];
		Print["\:7ebf\:6027\:65b9\:7a0b\:7ec4\:6c42\:89e3\:ff1a"<> ToString[Solc,TraditionalForm]];
		
		(*\:8ba1\:7b97\:96c5\:53ef\:6bd4*)
		condition=Flatten[{Eq,Eq2}];
		Jac=SchoutenSimplify[FullSimplify[Det[Table[D[condition[[i]],tau[[j]]],{j,Length[tau]},{i,Length[tau]}]]*SpinorAngleBracket[1,3]/SpinorSquareBracket[indexbar[[1]],indexbar[[2]]]]];
		
		
		SolJ=SchoutenSimplify[(FullSimplify[PolesProduct*Jtrees[[q]]/(Jac*Ct)])/.Solc];
		Print["\:6700\:7ec8\:7ed3\:679c\:4e3a"<>ToString[SolJ,TraditionalForm]];
		AppendTo[cSolution,Solc];
		AppendTo[JSolution,SolJ];
	];
	AppendTo[JtreesSolution,JSolution];
	AppendTo[ctreesSolution,cSolution];
]


(*\:5f85\:5b9a\:7cfb\:6570\:89e3\:65b9\:7a0b\:6c42\:89e3\:96c5\:53ef\:6bd4\:524d\:9762\:7684\:7cfb\:6570*)
Amp=ReplaceAll[expandSpinorBrackets[Total[grHelicityAmp[mm,mm,mm,pp,pp,pp]]],{ab->SpinorAngleBracket,sb->SpinorSquareBracket}];
Js=Flatten[JtreesSolution];
permtree1={{1->1},{1->2,2->1},{2->3,3->2}};
permtree2={{4->4},{4->5,5->4},{5->6,6->5}};
JoinPerm[a_,b_]:=Flatten[Table[Join[a[[i]],b[[j]]],{i,Length[a]},{j,Length[b]}],1];
perm=Range[6]/.JoinPerm[permtree1,permtree2];

Eq={};
B=Table[Subscript[b, i],{i,Length[Js]}];
For[j=1,j<=Length[B],j++,
	GenSpinors[{1,2,3,4,5,6},{AllMassless->True}];
	AppendTo[Eq,ToNum[Sum[B . myperm[Js,Range[6],perm[[i]]],{i,Length[perm]}]-Amp]];
	ClearKinematics
]

JacMP=Solve[Eq==0,B][[1]][[All,2]]
Eq/.Solve[Eq==0,B][[1]]


(*\:4fdd\:5b58\:7ed3\:679c*)
savefile=File["saved6pt.m"]
Save[savefile,{ctreesSolution,JtreesSolution,JacMP}]
