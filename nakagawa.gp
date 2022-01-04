\\ nakagawa.gp: Written by Henri Cohen (the hard parts) and Frank Thorne

\\ Runs numerical tests of our (HC, FT, and Simon Rubinstein-Salzedo) theorems 
\\ generalizing the Ohno-Nakagawa relations. 

/* Given quartic C_{\ell-1} field (checked), returns tau generator of Galois 
group, 0 if not C_{\ell-1} */

/* given automorphism tau as a polmod, compute tau^n naively (n small) */

powtau(tau,n)=
{
 my(res,vv);
 res=tau; vv=variable(lift(res));
 for (i=2,n,res=subst(lift(res),vv,tau));
 res;
}

/* compute degree ell-1 mirror field of Q(\sqrt{D}), assuming
D!=(-1)^{(ell-1)/2}\ell */

mirror(ell,D)=
{
 my(pol);
 if (D==(-1)^((ell-1)/2)*ell,error("special case in mirror"));
 pol=sum(k=0,(ell-1)/2,binomial(ell,2*k)*('y^2+4*D)^k*'y^(ell-1-2*k));
 pol/content(pol);
}

/* Given cyclic K as polynomial, compute generator of Gal(K/Q) */

computetau(K)=
{
 my(li,lm1,ct,tau,tauess,res,vv,fa,lfa,fl);
 lm1=poldegree(K); li=nfgaloisconj(K);
 if (#li!=lm1,return(0));
 ct=0; vv=variable(li[1]);
 fa=factor(lm1)[,1]; lfa=#fa;
 for(i=1,lm1,
  tauess=Mod(li[i],K); fl=1;
  for (j=1,lfa,
   if (lift(powtau(tauess,lm1/fa[j]))==vv,fl=0;break())
  );
  if (fl,tau=tauess;ct++)
 );
 if (ct!=eulerphi(lm1),return(0));
 return (tau);
}

/* compute list of powers of products of ramified prime ideals that
can occur as a conductor */

myideallist(bnf,B)=
{
 my(lm1,liram,Lram,Lrampr,p,lipr,vfor,llr);
 my(LLpr,LLfpr,bas,baspr);
 lm1=poldegree(bnf.pol);
 liram=factor(abs(bnf.disc))[,1]; llr=#liram; 
 Lram=vector(llr); Lrampr=vector(llr); vfor=vector(llr);
 for(i=1,llr,
  p=liram[i]; lipr=idealprimedec(bnf,p); tmp=matid(lm1);
  for (j=1,#lipr,tmp=idealmul(bnf,tmp,lipr[j]));
  Lram[i]=p^lipr[1][4]; Lrampr[i]=tmp;
  vfor[i]=[0,lipr[1][3]-1]
 );
 LLpr=[]; LLfpr=[];
 forvec(v=vfor,
  bas=prod(i=1,llr,Lram[i]^v[i]); if (bas>B,next());
  baspr=matid(lm1);
  for (i=1,llr,baspr=idealmul(bnf,baspr,idealpow(bnf,Lrampr[i],v[i])));
  LLpr=concat(LLpr,[baspr]); LLfpr=concat(LLfpr,[bas])
 );
 [LLpr,LLfpr];
}

isellpow(n,ell)=
{
 my(v);
 v=valuation(n,ell); return (n==ell^v);
}

/* flwitch[1]: give pols or not; flwitch[2]: give only powers of ell times suitable power of discriminant;
flwitch[3]: give number with exact discriminant; 
if vgg!=[], list of acceptable primroots */

Fellcommon(ell,K,B,sig=[],which,vgg=[])=
{ 
 my(lm1,drel,tau,bnf,L,bnr,W,li,H,DN,lcyc,gens,clgp,aa,aatau,lobnr,loaa,loaatau,Hinv,dd,ide,T,DD,ct);
 my(LLpr,LLfpr,nbll,bas,inn,polrel,polabs,rr1,pol,Lpro,Lfpro,flwhich,pro);
 lm1=poldegree(K); if ((ell-1)%lm1,error("incompatible degrees in Fell"));
 drel=(ell-1)\lm1; tau=computetau(K);
 if (tau==0,error("not a C_{ell-1} field in Fell"));
 r1=polsturm(K); 
 if(#sig && (#sig!=r1),error("incorrect number of archimedean places in Fell"));
 flwhich=[0,0,0]; for(i=1,3,if(which%2,flwhich[i]=1);which=which\2);
 bnf=bnfinit(K,1); DD=bnf.disc; pro=B^(1/drel);
 if (flwhich[3]==0,
  BD=ceil(pro/abs(DD)),
  BD=round(pro); 
  if (B!=BD^drel,return(0));
  if (BD%DD,return(0)); BD=BD\abs(DD); 
  flwhich[1]=0; flwhich[2]=0;
 );
 temp=myideallist(bnf,BD); 
 LLpr = temp[1]; LLfpr = temp[2];
 nbll=#LLfpr;
 if (flwhich[2],
  Lpro=[]; Lfpro=[];
  for (i=1,nbll,
   if (isellpow(LLfpr[i],ell),
    Lfpro=concat(Lfpro,[LLfpr[i]]); Lpro=concat(Lpro,[LLpr[i]])
   )
  );
  LLpr = Lpro; LLfpr = Lfpro; nbll=#LLfpr
 );
 if (flwhich[3],
  Lpro=[]; Lfpro=[];
  for (i=1,nbll,
   if (BD%LLfpr[i]==0,
    Lfpro=concat(Lfpro,[LLfpr[i]]); Lpro=concat(Lpro,[LLpr[i]])
   )
  );
  LLpr = Lpro; LLfpr = Lfpro; nbll=#LLfpr
 );
 W=[]; 
 if (#vgg==0,
  gg=znprimroot(ell)^drel; /* gg is of exact order (\ell-1)/drel = lm1 */
  nump=eulerphi(lm1); vgg=vector(nump); gh=1; ct=0;
  for (i=1,lm1-1,gh*=gg;if(gcd(i,lm1)==1,ct++;vgg[ct]=lift(gh))),
  nump=#vgg
 );
 for (in=1,nbll,
  bas=LLfpr[in];
  if (bas<=BD,
   if (flwhich[3],
    listn=[round((BD\bas)^(1/lm1))],
    if (flwhich[2]==0,
     listn=vector(ceil((BD/bas)^(1/lm1)),iii,iii),
     listn=vector(ceil(log(BD/bas)/(lm1*log(ell)))+1,a,ell^(a-1))
    )
   );
   for (ili=1,#listn,
    n=listn[ili]; 
    if (flwhich[3]==0 && flwhich[2]==0,
     if(!isellpow(gcd(n,DD),ell),next());
     if(!isellpow(core(n,1)[2],ell),next())
    );
    inn=n^lm1*bas; DN=(DD*inn)^drel; if (abs(DN)>B,break());
    if (flwhich[3] && inn!=BD,next());
    ide=n*LLpr[in];
    if (#sig,ide=[ide,sig]); bnr=bnrinit(bnf,ide,1); clgp=bnr.clgp;
    if (clgp[1]%ell,next());
    gens=clgp[3]; lcyc=#gens; T=Mat([]~); 
    for(j=1,lcyc,
     T=concat(T,Mat(bnrisprincipal(bnr,nfgaloisapply(bnf,tau,gens[j]),0)))
    );
    li=subgrouplist(bnr,[ell],0); 
    for(k=1,#li,
     H=li[k]; Hinv=ell*H^(-1);
     if (denominator(Hinv*T*H/ell)>1,next());
     for (ii=1,lcyc,
      if (H[ii,ii]==ell,
       aa=idealhnf(bnf,gens[ii]); loaa=bnrisprincipal(bnr,aa,0);
       aatau=nfgaloisapply(bnf,tau,aa); loaatau=bnrisprincipal(bnr,aatau,0);
       for(jj=1,nump,
        lobnr=Hinv*(loaatau-vgg[jj]*loaa)/ell;
        if (denominator(lobnr)==1,
         if (flwhich[1],
          polrel=rnfkummer(bnr,H); polabs=rnfequation(bnf,polrel);
          rr1=nfsubfields(polabs,ell); if (#rr1!=ell,error("not a F_ell (1)"));
          \\pol=polredbest(rr1[1][1]); 
          pol=polredabs(rr1[1][1]); 
          if (polgalois(pol)[1]!=ell*lm1,error("not a F_ell (2)")); 
          DN=[DN,pol]
         );
         W=concat(W,[DN]); break()
        )
       )
      )
     )
    )
   )
  )
 );
 if (flwhich[1], W=vecsort(W,1); W=vector(#W,i,W[i][2]), W=vecsort(W));
 return (W);
}

/* compute list of discriminants of F_\ell fields with resolvent cyclic
C_{(\ell-1)/d} K with discriminant <= B */ 
/* sig is the ramified places at infinity */

Fell(ell,K,B,sig=[],vgg=[])=Fellcommon(ell,K,B,sig,0,vgg);

/* Same but give polynomials instead, much slower */

Fellpol(ell,K,B,sig=[],vgg=[])=Fellcommon(ell,K,B,sig,1,vgg);

/* Restrict to discriminants of the form D^((ell-1)/2)*ell^a */

Fellspec(ell,K,B,sig=[],vgg=[])=Fellcommon(ell,K,B,sig,2,vgg);

/* Same but give polynomials instead, much slower */

Fellspecpol(ell,K,B,sig=[],vgg=[])=Fellcommon(ell,K,B,sig,3,vgg);

/* Give fields with exact discriminant EDI */

Fellexact(ell,K,EDI,sig=[],vgg=[])=Fellcommon(ell,K,EDI,sig,4,vgg);

/* Same but give polynomials instead, much slower */

Fellexactpol(ell,K,EDI,sig=[],vgg=[])=Fellcommon(ell,K,EDI,sig,5,vgg);

ND3(EDI)=
{
 #Fellexact(3,y^2-EDI,abs(EDI));
}

ND5(D,a)=
{
 #Fellexact(5,y^2-D,5^a*D^2)+#Fellexact(5,y^2-5*D,5^a*D^2);
}

ND7(D,a)=
{
 #Fellexact(7,y^2-D,7^a*abs(D)^3)+#Fellexact(7,y^2-7*D,7^a*abs(D)^3);
}

NF5(D,a)=
{
 #Fellexact(5,y^4+5*D*y^2+5*D^2,5^a*D^2);
}

NF7(D,a, primroot)=
{
 #Fellexact(7,y^6 + 7*D*y^4 + 14*D^2*y^2 + 7*D^3,abs(7^a*D^3),,primroot);
}

bnfQ=bnfinit('y);

myC4polsub(n)=my(res,w);res=polsubcyclo(n,4);if(#res==0,return(res));if(type(res)=="t_POL",res=[res]);w=[];for(i=1,#res,pol=res[i];if(polgalois(pol)[2]==-1&&rnfconductor(bnfQ,pol)[1][1]==Mat(n),w=concat(w,pol)));subst(w,'x,'y);

doC4pol(LIM)=my(w,res,ret);w=[];for(n=3,ceil(sqrt(LIM)/2),if(n%4!=2,res=myC4polsub(n);if(#res,ret=apply(nfdisc,res);for(i=1,#ret,if(ret[i]<=LIM,w=concat(w,[[ret[i],res[i]]]))))));w=vecsort(w,1);vector(#w,i,w[i][2]);

lll(i)=Fellpol(5,TABC4[i],10^7);

/*********************/
/* Some simple tests */


LHSNEG(D)=ND5(D,0)+ND5(D,2);
LHSPOS(D)=5*LHSNEG(D)+2;
RHS(D)=NF5(D,3)+NF5(D,5)+NF5(D,7);
{
test1() = 
  forstep(D=-3,-10000,-1,if(D%5 && isfundamental(D),
    if(LHSNEG(D)!=RHS(D),print("D = ");error("result is false"),print1("."))))
}


\\ prim_root: This is the particular value of g described in the presentation of F_l in the paper.

\\ Note: the values below were produced via trial and error. It would 
\\ be better to produce these automatically, but our tests were numerically
\\ feasible only through 13 anyway.

\\ For l = 1 (mod 4), the two primitive roots are additive inverses mod l.
{
prim_root(ell, sgn) = 
  retval = 0;
  if (ell == 5 && sgn == 1, retval = 3);
  if (ell == 5 && sgn == -1, retval = 2);
  if (ell == 7 && sgn == 1, retval = 5);
  if (ell == 7 && sgn == -1, retval = 3);
  if (ell == 11 && sgn == 1, retval = 2);
  if (ell == 11 && sgn == -1, retval = 6);
  if (ell == 13 && sgn == 1, retval = 11);
  if (ell == 13 && sgn == -1, retval = 2);
  \\ primitive roots mod 13: 2, 6, 7, 11
  if (retval == 0, print("Error in prim_root."));
  retval;
}

\\ test_thm_1: Test the main theorem for ell = 1 (mod 4).
\\ D_bound: Test for D_l fields of discriminant D and Dl with Dl < D_bound.
\\ sgn: sign of discriminants to be tested.
\\ verbose: If true, output more data.

\\ Outputs either a . or an X for each D successfully tested: . if the algorithm 
\\ checks that 0 = 0, X if some fields were found on each side.

\\ When not run in verbose mode, the program lumps fields of discriminant D and Dl together.
\\ The verbose mode outputs more detailed counts.

{
test_thm_1(ell, D_bound, sgn, verbose) = 
  l1 = (ell - 1)/2;
  forstep(D= sgn*3, sgn*D_bound,sgn,if(D%ell && isfundamental(D),
    mirror_field = mirror(ell, D);
    count1 = #Fellexact(ell,y^2-D,abs(D)^l1);
    count2= #Fellexact(ell,y^2-ell*D,(ell * abs(D))^l1);
    LHS = count1 + count2;
    if (verbose && LHS, print("LHS, l = ", ell, ", D = ", D, ", no *l= ", count1, ", w/ *l ", count2));
    RHS = 0;
    for (b = 0, l1, 
      disc_to_test = abs(D)^l1 * ell^(ell - 2 + 2*b);  
     count = #Fellexact(ell, mirror_field,disc_to_test,,[prim_root(ell, 1)]);
    if (verbose && count, print("RHS (+1), l = ", ell, ", D = ", D, ", b = ", b, ", count = ", count));
     RHS = RHS + count;
    );
    for (b = 0, l1, 
      disc_to_test = abs(ell * D)^l1 * ell^((ell - 3)/2 + 2*b);
      count = #Fellexact(ell, mirror_field,disc_to_test,,[prim_root(ell, -1)]);
      if (verbose && count, print("RHS (-1), l = ", ell, ", D = ", D, ", b = ", b, ", count = ", count));
      RHS = RHS + count;
    );
   if (sgn == 1, LHS = ell * LHS + 2);
   if (LHS == RHS && LHS == 0 && !verbose, print1("."));
   if (LHS == RHS && LHS > 0 && !verbose, print1("X"));
   if (LHS != RHS, error("Mismatch : ", LHS, ", ", RHS));
   ));
}

\\ test_thm_3: Basically the same as test_thm_1, only for \ell = 3 (mod 4).
\\ One difference is that the mirror fields are now different for Q(\sqrt{D}) and Q(\sqrt{\ell D}),
\\ so it doesn't make sense to combine the counts. So the counts are done separately,
\\ with X or O displayed for D and l*D respectively.

{
test_thm_3(ell, D_bound, sgn, verbose) = 
  l1 = (ell - 1)/2;
  forstep(D=sgn*3,sgn*D_bound,sgn,if(D%ell && isfundamental(D),
    mirror_field = mirror(ell, D);
    LHS = #Fellexact(ell,y^2-D,abs(D)^l1);
    if (verbose && LHS, print("LHS (-), l = ", ell, ", D = ", D, ", count = ", LHS));
    RHS = 0;
    for (b = 0, l1, 
      disc_to_test = abs(D)^l1 * ell^(ell - 2 + 2*b);  
      count = #Fellexact(ell, mirror_field,disc_to_test,,[prim_root(ell, 1)]);
      if (verbose && count, print("RHS (-), l = ", ell, ", D = ", D, ", b = ", b, ", count = ", count));
      RHS = RHS + count;
    );
   if (sgn == 1, LHS = ell * LHS + 1);
   if (LHS == RHS && LHS == 0 && !verbose, print1("."));
   if (LHS == RHS && LHS > 0 && !verbose, print1("X"));
   if (LHS != RHS, error("Mismatch : ", LHS, ", ", RHS));
   );
   if (D%ell && isfundamental(ell * D),
    mirror_field = mirror(ell, ell * D);
    LHS = #Fellexact(ell,y^2-(ell * D),abs(ell * D)^l1);
    if (verbose && LHS, print("LHS (l), l = ", ell, ", D = ", D, ", count = ", LHS));
    RHS = 0;
    for (b = 0, l1, 
     if (b != 1,
        disc_to_test = abs(ell * D)^l1 * ell^((ell - 5)/2 + 2*b);
        count = #Fellexact(ell, mirror_field,disc_to_test,,[prim_root(ell, 1)]);
        if (verbose && count, print("RHS (l), l = ", ell, ", D = ", D, ", b = ", b, ", count = ", count));
        RHS = RHS + count;
    );
    );
   if (sgn == 1, LHS = ell * LHS + 1);
   if (LHS == RHS && LHS == 0 && !verbose, print1("."));
   if (LHS == RHS && LHS > 0 && !verbose, print1("O"));
   if (LHS != RHS, error("Mismatch : ", LHS, ", ", RHS));
   );
  );
}

\\ test_thm: Tests the main theorem, for ell as given, and for D and \ell*D with |D| < D_bound.
\\ sgn gives the sign of the discriminant.
{
test_thm(ell, D_bound, sgn, verbose=0) = 
  if (Mod(ell, 4) == Mod(1, 4),
    test_thm_1(ell, D_bound, sgn, verbose),
    test_thm_3(ell, D_bound, sgn, verbose)
  );
}


\\ test_D: Looks for all D_l and F_l fields with quadratic resolvent
\\ D or ell*D, or one of their mirror fields.

\\ Does not zero in only on the fields we are counting, so displays some irrelevant information.
\\ Also, can displays fields twice, e.g. for \ell = 1 (mod 4) in which case mf1 and mf2 are the
\\ same field.

\\ Note: Is this behavior correct?
\\ ? Fellexactpol(5, y^2 - 401, 401^2,,[4])
\\ %15 = [160801]

{
test_D(ell, D) = 
 my(i, j, F);
 field_fn = Fellexactpol;
 mf1 = mirror(ell, D);
 mf2 = mirror(ell, ell*D);
 l1 = (ell - 1)/2;
 for (j = 1, ell - 1, 
   if (1 == 1, 
   \\ if (znorder(Mod(j, ell)) == ell - 1, 
   for (i = 0, 2*ell, 
     F= field_fn(ell, y^2 - D, abs(D)^l1*ell^i,,[j]);
     if (#F > 0, print("[D: ] i = ", i, "; j = ", j, ":", F));
     F=  field_fn(ell, y^2 - D*ell, abs(ell*D)^l1*ell^i,,[j]);
     if (#F > 0, print("[D:*] i = ", i, "; j = ", j, ":", F));
     F=  field_fn(ell, mf1, abs(D)^l1*ell^i,,[j]);
     if (#F > 0, print("[F: ] i = ", i, "; j = ", j, ":", F));
     F=  field_fn(ell, mf2, abs(ell*D)^l1*ell^i,,[j]);
     if (#F > 0, print("[F:*] i = ", i, "; j = ", j, ":", F));
   );
 ));
}
 

\\ i don't think this worked for 7... 
{
test_temp(ell, D_bound, sgn) = 
 my(i, j, F);
 forstep(D=sgn*3,sgn*D_bound,sgn,if(D%ell && isfundamental(D),
 mf1 = mirror(ell, D);
 l1 = (ell - 1)/2;
 mf2 = mirror(ell, (-1)^l1*ell*D);
   for (i = ell - 2, 2*ell - 3, 
     j = prim_root(ell, 1);
     F=  Fellexact(ell, mf1, abs(D)^l1*ell^i,,[prim_root(ell, 1)]);
     if (#F > 0, print("[F: ] i = ", i, "; j = ", j, ":", F));
     j = prim_root(ell, 1);
     F=  Fellexact(ell, mf1, abs(D)^l1*ell^i,,[prim_root(ell, -1)]);
     \\ F=  Fellexact(ell, mf2, abs(D)^l1*ell^i,,[prim_root(ell, 1)]);
     if (#F > 0, print("[F:*] i = ", i, "; j = ", j, ":", F));
 )));
}

{
test_temp2(ell, D_bound, sgn) = 
 my(i, j, F);
 forstep(D=sgn*3,sgn*D_bound,sgn,if(D%ell && isfundamental(D),
 mf1 = mirror(ell, D);
 l1 = (ell - 1)/2;
 mf2 = mirror(ell, (-1)^l1*ell*D);
 for (j = 1, ell - 1, 
   if (znorder(Mod(j, ell)) == ell - 1, 
   for (i =  ell - 2, 2*ell - 3,
     F=  Fellexact(ell, mf1, abs(D)^l1*ell^i,,[j]);
     if (#F > 0, print("[F: ] i = ", i, "; j = ", j, ":", F));
     F=  Fellexact(ell, mf2, abs(ell*D)^l1*ell^i,,[j]);
     if (#F > 0, print("[F:*] i = ", i, "; j = ", j, ":", F));
   );
 ))));
}
  
{
test104() = 
 my(a);
 for (a = 1, 2000,
   if (a == 2000, a = 68381);
   nf = Fellexact(5,y^2-13,abs(13^2*a^4));
   if (#nf > 0, print("a = ", a, " # fields = ", nf, " ", Mod(a, 65)));
 );
}

K5 = bnfinit(x^5 + 5*x^3 + 5*x - 3);
K7 = bnfinit(x^7 - 14*x^5 + 56*x^3 - 56*x - 15);
{
test104b(KK, D, l) =
 my(a);
 for (a = 1, 1000,
   if (isprime(a),
     if (Mod(kronecker(D, a), l) == Mod(a, l),
        print(a, ": ", length(idealprimedec(KK, a)));
 )));
}

test104b1() = test104b(K7, -287, 7);

{
test104c() = 
 my(a);
 for (a = 1, 2000,
   if (a == 2000, a = 2359);
   nf = Fellexact(7,y^2+287,abs(287^3*a^6));
   if (#nf > 0, print("a = ", a, " # fields = ", #nf));
 );
}
