\\\\\\\\\\\\\\\\\\\\\\\\\\\\
\\ Sym2(2)2--Pairs of binary quadratic forms
\\\\\\\\\\\\\\\\\\\\\\\\\\\\


p1=p-1;
p2=p^2-1;
q1=p2/p1;


\\\\\\\\\\\\\\\\\\\\\\\\\\\\
\\ orbit size;
\\\\\\\\\\\\\\\\\\\\\\\\\\\\
ors=[1,q1*p2,p*q1*p2/2,p*p1*p2/2,p*p2^2,p^2*p2^2/2,p^2*p1^2*p2/2];
ORS=matdiagonal(ors);


\\\\\\\\\\\\\\\\\\\\\\\\\\\\
\\ Counting elements in subspaces
\\\\\\\\\\\\\\\\\\\\\\\\\\\\


W00=[1,0,0,0,0,0,0];
W11=[1,p2,0,0,0,0,0];
W02=[1,p1,p*p1,0,0,0,0];
W03=[1,p2,p*p2/2,p*p1^2/2,0,0,0];
W13=[1,(2*p+1)*p1,p*p2/2,p*p1^2/2,p*p1^2,p^2*p1^2,0];
u1d=[1,1/q1,2/q1,0,1/q1,0,0];
W22=vector(7,i,u1d[i]*ors[i]);
W33=ors;



\\\\\\\\\\\\\\\\\\\\\\\\\\\\
\\ Create a matrix from counts
\\\\\\\\\\\\\\\\\\\\\\\\\\\\
W=matrix(7,7);
for(i=1,7,W[i,1]=W00[i]);
for(i=1,7,W[i,2]=W33[i]);
for(i=1,7,W[i,3]=W11[i]);
for(i=1,7,W[i,4]=W22[i]);
for(i=1,7,W[i,5]=W02[i]);
for(i=1,7,W[i,6]=W13[i]);
for(i=1,7,W[i,7]=W03[i]);

{
if(matrank(W)==7,
	print("We can and do compute the matrix M"),
	print("We can NOT compute the matrix M correctly")
);
}


\\\\\\\\\\\\\\\\\\\\\\\\\\\\
\\ Compute the matrix M \\
\\\\\\\\\\\\\\\\\\\\\\\\\\\\

bm(k)=[0,p^(6-k);p^k,0];
Mprime=matconcat(matdiagonal([bm(0),bm(2),bm(2),p^3]));
U=matrix(7,7);
U=ORS^(-1)*W;
M=U*Mprime*U^(-1);
print("M is computed:")

print("The Matrix M:");
print(M);


\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\
\\ Check that M satisfy Lemma 6 \\
\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\

T=p^2*p1*p2^2*ORS^(-1);
TBZ=M*T-(M*T)~;

{
if(TBZ==matrix(7,7),
	print("  -- M is symmetric in the sense of Lemma 6"),
	print("  -- M is NOT symmetric in the sense of Lemma 6")
);
}

{
if(M*M==p^(6)*matid(7),
	print("  -- M^2 is the scalar matrix"),
	print("  -- M^2 is NOT the scalar matrix")
);
}



\\\\\\\\\\\\\\\\\\\\\\\\\\\\
\\ Compute some Fourier transforms
\\\\\\\\\\\\\\\\\\\\\\\\\\\\
sing=[1,1,1,1,1,0,0];
quad=[0,0,0,0,0,1,-1];

print("* Fourier transform of singular sets:");
print(M*sing~);
print("* Fourier transform of the quadratic charcter:");
print(M*quad~);
