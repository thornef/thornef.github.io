\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\
\\ 2Sym2(3)--Pairs of ternary quadratic forms
\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\

\\ *** NOT FINISHED. ***

p1=p-1;
p2=p^2-1;
p3=p^3-1;
q1=p2/p1;
q2=p3/p1;

r=20;
d=12;

\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\
\\ Orbit Size
\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\


sz(a,b)=p1^a*p^b*q1^2*q2;

size(a,b,c,d) = (p - 1)^a * p^b * (p + 1)^c * (p^2 + p + 1)^(d/2);

{
ors2=[
1,size(1,0,1,2),size(1,1,2,2)/2,size(2,1,1,2)/2,size(2,2,1,2),
size(2,1,2,2),size(2,3,1,2),size(2,2,2,2)/2,size(3,2,1,2)/2,size(3,2,2,2),size(3,3,2,2),
size(3,4,1,2)/2,size(2,4,2,2)/2,size(3,4,2,2)/2,size(3,4,2,2)/2,
size(4,4,2,2)/24,size(4,4,2,2)/4,size(4,4,2,2)/8,size(4,4,2,2)/3,size(4,4,2,2)/4];
}

{
ors=[
1,q1*p3,p*p3*q1^2/2,p*p3*p2/2,p^2*p2*p3,
	\\5	0,D1^2,D11,D2,Dns
q2*q1*p2*p1*p,q2*p^3*p2*p1,
	\\2	Cs,Cns
1/2*sz(2,2),1/2*sz(3,2)/q1,
	\\2	B11,B2
sz(3,2),sz(3,3),sz(3,4)/q1/2,sz(2,4)/2,
	\\4	1^4,1^31,2^2,1^21^2
sz(3,4)/2,sz(3,4)/2,
	\\2	1^211,1^22
sz(4,4)/24,sz(4,4)/4,sz(4,4)/8,sz(4,4)/3,sz(4,4)/4
	\\5	1111,112,22,13,4
]
};

\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\
\\ Counting elements in subspaces
\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\

\\=============================================
\\ Counts of Wij for i=0 or j\leq 3
\\=============================================

W00=[1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0];
W01=[1,p1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0];
W02=[1,p1,p*p1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0];
W03=p*p1*[0,1,p1/2,p1/2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]+W02;
W04=[1,p2,p*p1*(3*p+1)/2,p*p1^2/2,p^2*p1^2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0];
W05=[1,p2,(2*p+1)*p*p2/2,p*p1^2/2,p^2*p2*p1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0];
W06=[1,p3,p*q1*p3/2,p*p1*p3/2,p^2*p1*p3,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0];

W11=[1,p2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0];
W12=p*p1^2*[0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0]+W02+W11-W01;
W13=p^2*p1^2*[0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0]+W03+W12-W02;
W22=p*p1*p2*[0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0]+q1*W02-p*W00;
W23=p^2*p1^2*[0,0,0,0,0,1,0,p1/2,p1/2,0,0,0,0,0,0,0,0,0,0,0]+W13+W22-W12;
W33=p^2*p1*p2*[0,0,0,0,0,1,0,p1/2,p1/2,0,0,0,0,0,0,0,0,0,0,0]+q1*W13-p*W11;



\\=============================================
\\ (I) -- Counts of W14,W15,W16,W24,W25,W26,W44
\\=============================================

W14=p^2*p1^2*[0,0,0,0,0,1,0,0,0,p1,0,0,0,0,0,0,0,0,0,0]+W04+W13-W03;
W15=[0,0,0,0,0,0,0,0,0,0,0,0,p^4*p1^2,0,0,0,0,0,0,0]+W14+W05-W04;
W16=p^3*p1^2*[0,0,0,0,0,0,0,1,0,p1,0,p*p1/2,p*p1/2,0,0,0,0,0,0,0]+W06+W15-W05;

W24=p^3*p1^2*[0,0,0,0,0,0,1,0,0,0,p1,0,0,0,0,0,0,0,0,0]+W14+W23-W13;
W25=p^3*p1^2*[0,0,0,0,0,0,1,0,0,0,p1,0,0,p*p1,0,0,0,0,0,0]+W15+W24-W14;
W26=p^4*p1^2*[0,0,0,0,0,0,0,0,0,0,0,0,1,p1,p1,p1^2/4,p1^2/2,p1^2/4,0,0]+W16+W25-W15;

W44=p*p1*p2*p^3*[0,0,0,0,0,0,0,0,0,0,0,0,1,p1/2,p1/2,0,0,0,0,0]+q1*W24-p*W22;

\\=============================================
\\ Total space -- W66
\\=============================================

W66=ors;

\\=============================================
\\ (II) -- Counts of W1,W2,W3,W4,W5
\\=============================================

W1=[1,p1,p*p2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0];\\[0,0,*,0,*,*]
W2=[1,p2,p*p2,0,0,p*p1*p2,0,0,0,0,0,0,0,0,0,0,0,0,0,0];
W3=p*p1*p2*[0,0,0,0,0,0,p^2,0,0,0,0,0,0,0,0,0,0,0,0,0]+q1*W2-p*W11;
W4=[1,2*p1,p1^2/2,p1^2/2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0];
W5=p*p1*p2*[0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0]+q1*W4-p*W00;

\\=============================================
\\ (III) -- Counts by common zeros -- W55,W6
\\=============================================

cz=[q2,q1,2*p+1,1,q1,q1,p+2,1,1,1,2,0,2,3,1,4,2,0,1,0];

U55=vector(20,i,cz[i]/cz[1]);
W55=vector(20,i,U55[i]*ors[i]);
U6=vector(20,i,cz[i]*(cz[i]-1)/cz[1]/(cz[1]-1));
W6=vector(20,i,U6[i]*ors[i]);


\\=============================================
\\ (IV) -- One more space -- W7
\\=============================================

{
U7=
[1,p2,p*p2/2,p*p1^2/2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
+p2*[0,0,1,0,0,p1,p*p1,0,0,0,0,0,0,0,0,0,0,0,0,0]
+p2*p1*p*[0,0,0,0,0,0,0,0,0,0,0,0,1,p1/2,p1/2,0,0,0,0,0]
};

{
W7=
p1*[0,1,0,0,0,0,0,p2,0,0,0,p*p1^2/2,p*p2/2,0,0,0,0,0,0,0]
+p1*p2*[0,0,1,0,0,0,0,p1,0,0,0,0,p*p1,p*p1,0,p*p1^2/2,0,p*p1^2/2,0,0]
+U7
};

\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\
\\ Create a matrix from counts
\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\

W=matrix(20,20);

\\---- 8 orthogonal pairs
for(i=1,20,W[i,1]=W00[i]);
for(i=1,20,W[i,2]=W66[i]);
for(i=1,20,W[i,3]=W11[i]);
for(i=1,20,W[i,4]=W55[i]);
for(i=1,20,W[i,5]=W04[i]);
for(i=1,20,W[i,6]=W26[i]);
for(i=1,20,W[i,7]=W05[i]);
for(i=1,20,W[i,8]=W16[i]);
for(i=1,20,W[i,9]=W14[i]);
for(i=1,20,W[i,10]=W25[i]);
for(i=1,20,W[i,11]=W22[i]);
for(i=1,20,W[i,12]=W44[i]);
for(i=1,20,W[i,13]=W33[i]);
for(i=1,20,W[i,14]=W3[i]);
for(i=1,20,W[i,15]=W5[i]);
for(i=1,20,W[i,16]=W6[i]);
\\---- 4 of self-orthogonal subspaces
for(i=1,20,W[i,17]=W06[i]);
for(i=1,20,W[i,18]=W15[i]);
for(i=1,20,W[i,19]=W24[i]);
for(i=1,20,W[i,20]=W7[i]);

{
if(matrank(W)==20,
	print("We can and do compute the matrix M"),
	print("We can NOT compute the matrix M correctly")
);
}

M1 = matrix(20, 20);
M2 = matrix(20, 20);

for(i=1,20,M1[1,i]=W00[i]/ors[i]);
for(i=1,20,M1[2,i]=W66[i]/ors[i]);
for(i=1,20,M1[3,i]=W11[i]/ors[i]);
for(i=1,20,M1[4,i]=W55[i]/ors[i]);
for(i=1,20,M1[5,i]=W04[i]/ors[i]);
for(i=1,20,M1[6,i]=W26[i]/ors[i]);
for(i=1,20,M1[7,i]=W05[i]/ors[i]);
for(i=1,20,M1[8,i]=W16[i]/ors[i]);
for(i=1,20,M1[9,i]=W14[i]/ors[i]);
for(i=1,20,M1[10,i]=W25[i]/ors[i]);
for(i=1,20,M1[11,i]=W22[i]/ors[i]);
for(i=1,20,M1[12,i]=W44[i]/ors[i]);
for(i=1,20,M1[13,i]=W33[i]/ors[i]);
for(i=1,20,M1[14,i]=W3[i]/ors[i]);
for(i=1,20,M1[15,i]=W5[i]/ors[i]);
for(i=1,20,M1[16,i]=W6[i]/ors[i]);
for(i=1,20,M1[17,i]=W06[i]/ors[i]);
for(i=1,20,M1[18,i]=W15[i]/ors[i]);
for(i=1,20,M1[19,i]=W24[i]/ors[i]);
for(i=1,20,M1[20,i]=W7[i]/ors[i]);



for(i=1,20,M2[2,i]=p^12 * W00[i]/ors[i]);
for(i=1,20,M2[1,i]=W66[i]/ors[i]);
for(i=1,20,M2[4,i]=p^10 * W11[i]/ors[i]);
for(i=1,20,M2[3,i]=p^2 * W55[i]/ors[i]);
for(i=1,20,M2[6,i]=p^8 * W04[i]/ors[i]);
for(i=1,20,M2[5,i]=p^4 * W26[i]/ors[i]);
for(i=1,20,M2[8,i]=p^7 * W05[i]/ors[i]);
for(i=1,20,M2[7,i]=p^5 * W16[i]/ors[i]);
for(i=1,20,M2[10,i]=p^7 * W14[i]/ors[i]);
for(i=1,20,M2[9,i]=p^5 * W25[i]/ors[i]);
for(i=1,20,M2[12,i]=p^8*W22[i]/ors[i]);
for(i=1,20,M2[11,i]=p^4 * W44[i]/ors[i]);
for(i=1,20,M2[14,i]=p^6 * W33[i]/ors[i]);
for(i=1,20,M2[13,i]=p^6 * W3[i]/ors[i]);
for(i=1,20,M2[16,i]=p^8 * W5[i]/ors[i]);
for(i=1,20,M2[15,i]=p^4 * W6[i]/ors[i]);
for(i=1,20,M2[17,i]=p^6 * W06[i]/ors[i]);
for(i=1,20,M2[18,i]=p^6 * W15[i]/ors[i]);
for(i=1,20,M2[19,i]=p^6 * W24[i]/ors[i]);
for(i=1,20,M2[20,i]=p^6 * W7[i]/ors[i]);

MM = (M1^-1 * M2)~;
\\ verified same as M.


\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\
\\ Compute the matrix M \\
\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\


bm(k)=[0,p^(d-k);p^k,0];
Mprime=matconcat(matdiagonal([bm(0),bm(2),bm(4),bm(5),bm(5),bm(4),bm(6),bm(4),p^6,p^6,p^6,p^6]));

ORS=matdiagonal(ors);
U=ORS^(-1)*W;


M=U*Mprime*U^(-1);
degM=matrix(r,r);
for(i=1,r,for(j=1,r,if(M[i,j]==0,degM[i,j]=z,degM[i,j]=poldegree(M[i,j],p))));

\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\
\\ Check that M satisfy Lemma 6 \\
\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\


T=p*p1*p2*p^3*p1*p2*p3/p1*ORS^(-1);
TBZ=M*T-(M*T)~;

{
if(TBZ==matrix(r,r),
	print("  -- M is symmetric in the sense of Lemma 6"),
	print("  -- M is NOT symmetric in the sense of Lemma 6")
);
}

{
if(M*M==p^(d)*matid(r),
	print("  -- M^2 is the scalar matrix"),
	print("  -- M^2 is NOT the scalar matrix")
);
}

	
\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\
\\ Compute some Fourier transforms
\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\

sing=[1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,0,0,0,0,0];
quad=[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,-1,1,1,-1];

print("* Fourier transform of singular sets:");
for(i=1,20,print((M*sing~)[i]));
print("* Fourier transform of the quadratic charcter:");
print(M*quad~);

phi2 = p^2 + p + 1;
f(a, b, c) = (p - 1)^a * p^b * (p + 1)^c;
a1 = p - 2;
a2 = p - 3;
a3 = 2*p - 1;
a4 = 2*p + 1;
a5 = 2*p - 3;
a6 = 3*p - 1;
a7 = 3*p + 1;
a8 = 5*p - 7;
b(i) = p^2 + i;
c1 = p^2 - p - 1;
c2 = p^2 - p + 1;
c3 = p^2 - 2*p - 1;
c4 = p^2 + 2*p - 1;
c5 = p^2 - 2*p + 3;
c6 = p^2 - 4*p - 1;
c7 = 2*p^2 + p + 1;
c8 = 2*p^2 +2*p + 1;
c9 = 2*p^2 -5*p - 1;
c10 = 3*p^2 - p - 1;
c11 = 3*p^2 - 2*p + 1;
c12 = 3*p^2 +3*p + 1;
d1 = p^3 - p - 1;
d2 = p^3 - p^2 + 1;
d3 = p^3 - p^2 - p - 1;
d4 = p^3 + p^2 - p + 1;
d5 = p^3 - p^2 - 2*p - 1;
d6 = p^3 + p^2 - 3*p - 1;
d7 = p^3 - 2*p^2 +p + 1;
d8 = p^3 - 2*p^2 +2*p - 2;
d9 = p^3 - 4*p^2 + p + 1;
d10 = 2*p^3 - p^2 - 2*p - 1;
e1 = p^4 + 1;
e2 = p^4 - p^3 + 1;
e3 = p^4 + 2*p^3 - 2*p^2 - 2*p - 1;
e4 = 2*p^4 - 2*p^3 - p^2 + p + 1;

{
test(i, j, rh) = 
  if (M[i, j] != rh,
    print("Error :", i, ", ", j);
);
}
x(i, j, foo) = test(i, j, foo);
y(i, j, a, b, c, foo) = test(i, j, f(a, b, c)*foo);
yy(i, j, a, b, c, foo) = test(i, j, f(a, b, c)*foo/2);
y24(i, j, a, b, c, foo) = test(i, j, f(a, b, c)*foo/24);
y8(i, j, a, b, c, foo) = test(i, j, f(a, b, c)*foo/8);
y3(i, j, a, b, c, foo) = test(i, j, f(a, b, c)*foo/3);
y4(i, j, a, b, c, foo) = test(i, j, f(a, b, c)*foo/4);

z(i, j) = test(i, j, 0);

print("2:------");
y(1, 2, 1,0,1, phi2);
x(2, 2, d1);
y(3, 2, 1,0,0, c8);
y(4, 2, 0,0,1, -1);
x(5, 2, d1);
x(6, 2, d1);
y(7, 2, 1, 0, 2, 1);
y(8, 2, 0,0,1, -1);
y(9, 2, 0,0,1, -1);
y(10, 2, 0,0,1, -1);
x(11, 2, c1);
x(13, 2, c1);
x(12, 2, -phi2);
y(14, 2, 1,0,0, a4);
y(15, 2, 0,0,1, -1);
x(16, 2, c10);
x(17, 2, c1);
x(18, 2, -phi2);
y(19, 2, 0,0,1, -1);
x(20, 2, -phi2);

print("3:------");
yy(1, 3, 1,1,2, phi2);
yy(2, 3, 1,1,1, c8);
yy(3, 3, 0,1,0, e3);
yy(4, 3, 1,1,3, 1);
yy(5, 3, 0,1,1,d1);
yy(6, 3, 0,1,0,d10);
yy(7, 3, 0,1,1, c3);
yy(8, 3, 1,1,0, c12);
yy(9, 3, 0,1,1, c1);
yy(10,3,  0,1,1, c1);
yy(11, 3, 0,1,0, -a7);
yy(13, 3, 0,1,0,d6);
yy(12, 3, 1,1,2, 1);
yy(14, 3, 0,1,0,c6);
yy(15, 3, 0,1,0,c3);
yy(16, 3, 0,1,0,c9);
yy(17, 3, 0,1,0,-a7);
yy(18, 3, 1,1,0,a4);
yy(19, 3, 0,1,2,-1); 
yy(20, 3, 0,1,1,-1);


print("4:------");
yy(1, 4, 2,1,1, phi2);
yy(2, 4, 1,1,1, -1);
yy(3, 4, 2,1,2, 1);
yy(4, 4, 0,1,0,e1);
yy(5, 4, 1,1,0,d1);
yy(6, 4, 1,1,1,-1);
yy(7, 4, 2,1,1,1);
yy(8, 4, 1,1,0,-phi2);
yy(9, 4, 0,1,1,c2);
yy(10,4,  1,1,0,-phi2);
yy(11, 4, 1,1,0,-1);
yy(13, 4, 1,1,0,-b(1));
yy(12, 4, 0,1,0,-d3);
yy(14, 4, 2,1,0,1);
yy(15, 4, 0,1,0,b(1));
yy(16, 4, 1,1,0,a3);
yy(17, 4, 1,1,0,-1);
yy(18, 4, 0,1,0,c7);
yy(19, 4, 1,1,1,-1);
yy(20, 4, 0,1,1,1);

print("5:------");
y(1, 5, 2,2,1, phi2);
y(2, 5, 1,2,0, d1);
y(3, 5, 1,2,0, d1);
y(4, 5,1,2,0, d1);
y(5, 5, 0,2,0,e2);
y(6, 5, 1,2,1,-1);
y(7, 5, 1,2,1,-1);
y(8, 5, 1,2,1,-1);
y(9, 5, 1,2,1,-1);
y(10, 5, 0,2,0,1);
y(11, 5, 0,2,0,1);
y(13, 5, 1,2,0,-1);
y(12, 5, 1,2,0,-1);
y(14, 5, 1,2,0,-1);
y(15, 5, 1,2,0,-1);
y(16, 5, 0,2,0,-a3);
y(17, 5, 0,2,0,1);
y(18, 5, 0,2,0,-a3);
y(19, 5, 0,2,1,1);
y(20, 5, 0,2,0,1);

print("6:------");
y(1, 6, 2,1,2, phi2);
y(2, 6, 1,1,1, d1);
y(3, 6, 1,1,0, d10);
y(4, 6,1,1,2,-1)
y(5, 6, 1,1,2,-1);
y(6, 6, 0,1,0,e4);
y(7, 6, 1,1,1,c1);
y(8, 6, 1,1,0,d5);
y(9, 6, 0,1,1,d2);
y(10, 6, 0,1,0,-c1);
y(11, 6, 0,1,0,d7);
y(13, 6, 1,1,0,c3);
y(12, 6, 1,1,2,-1);
y(14, 6, 0,1,0,d9);
y(15, 6, 0,1,0,d7);
y(16, 6, 0,1,0,-a3*a7);
y(17, 6, 1,1,0,-a4);
y(18, 6, 1,1,0,-a4);
y(19, 6, 0,1,1,1);
y(20, 6, 0,1,1,1);


print("7:------");
y(1, 7, 2,3,1, phi2);
y(2, 7, 2,3,2, 1);
y(3, 7, 1,3,0,c3);
y(4, 7,2,3,1,1)
y(5, 7, 1,3,1,-1);
y(6, 7, 1,3,0,c1);
y(7, 7, 0,3,0, -b(-2));
y(8, 7, 2,3,1,1);
y(9, 7, 2,3,1,1);
y(10, 7, 1,3,0,-1);
y(11, 7, 0,3,0,-a1);
y(13, 7, 1,3,0,-2);
y(12, 7, 1,1,2,0);
y(14, 7, 0,3,0,-a2);
y(15, 7, 1,3,0,-1);
y(16, 7, 0,3,0,4);
y(17, 7, 0,3,0,2);
y(18, 7, 1,1,1,0);
y(19, 7, 0,3,0,1);
y(20, 7, 0,1,1,0);

print("8:------");
yy(1, 8, 2,2,2, phi2);
yy(2, 8, 1,2,2, -1);
yy(3, 8, 2,2,0, c12);
yy(4, 8, 1,2,1,-phi2);
yy(5, 8, 1,2,2,-1);
yy(6, 8, 1,2,0,d5);
yy(7, 8, 2,2,2,1);
yy(8, 8, 0,2,0,-d3);
yy(9, 8, 1,2,2,-1);
yy(10,8,  0,2,1,1);
yy(11, 8, 1,2,1,-1);
yy(13, 8, 1,2,1,-1);
yy(12, 8, 0,2,2,1);
yy(14, 8, 1,2,0,-1);
yy(15, 8, 1,2,0,-a4);
yy(16, 8, 0,2,0,c11);
yy(17, 8, 1,2,1,-1);
yy(18, 8, 0,2,0,-c3);
yy(19, 8, 0,2,1,1);
yy(20, 8, 0,2,2,1);


print("9:------");
yy(1, 9, 3,2,1, phi2);
yy(2, 9, 2,2,1, -1);
yy(3, 9, 2,2,0, c1);
yy(4, 9, 1,2,1,c2);
yy(5, 9, 2,2,1,-1);
yy(6, 9, 1,2,0,d2);
yy(7, 9, 3,2,1,1);
yy(8, 9, 2,2,1,-1);
yy(9, 9, 0,2,0,-d4);
yy(10,9,  1,2,0,1);
yy(11, 9, 2,2,0,-1);
yy(13, 9, 2,2,0,-1);
yy(12, 9, 1,2,1,1);
yy(14, 9, 1,2,0,-a3);
yy(15, 9, 1,2,0,1);
yy(16, 9, 1,2,0,-a6);
yy(17, 9, 0,2,0,c4);
yy(18, 9, 1,2,1,1);
yy(19, 9, 1,2,0,1);
yy(20, 9, 0,2,0,-b(1));

print("10:------");
y(1, 10, 3,2,2, phi2);
y(2, 10, 2,2,2,- 1);
y(3, 10, 2,2,1,c1);
y(4, 10,2,2,1,-phi2)
y(5, 10, 1,2,1,1);
y(6, 10, 1,2,0,-c1);
y(7, 10, 2,2,1, -1);
y(8, 10, 1,2,1,1);
y(9, 10, 1,2,1,1);
y(10, 10, 0,2,0,-1);
y(11, 10, 1,2,0,b(1));
y(13, 10, 2,2,0,-1);
y(12, 10, 1,2,1,1);
y(14, 10, 3,2,0,1);
y(15, 10, 2,2,1,-1);
y(16, 10, 0,2,0,-a3*a6);
y(17, 10,1,2,0,1);
y(18, 10, 0,2,1,a3);
y(19, 10, 0,2,1,-1);
y(20, 10, 0,2,1,-1);



print("11:------");
y(1, 11, 3,3,2, phi2);
y(2, 11, 2,3,1,c1);
y(3, 11, 2,3,0,-a7);
y(4, 11,2,3,1,-1)
y(5, 11, 1,3,1,1);
y(6, 11, 1,3,0,d7);
y(7, 11, 1,3,1, -a1);
y(8, 11, 2,3,1,-1);
y(9, 11, 2,3,1,-1);
y(10, 11, 1,3,0,b(1));
y(11, 11, 0,3,0,d8);
y(13, 11, 2,3,0,-2);
y(12, 11, 1,2,1,0);
y(14, 11, 1,3,0,-a5);
y(15, 11, 1,3,0,1);
y(16, 11, 0,3,0, 4*a3);
y(17, 11,0,3,0,-2);
y(18, 11, 0,2,1,0);
y(19, 11, 0,3,1,-1);
y(20, 11, 0,2,1,0);

print("13:------");
yy(1, 13, 2,4,2, phi2);
yy(2, 13, 1,4,1,c1);
yy(3, 13, 1,4,0,d6);
yy(4, 13,1,4,1,-b(1))
yy(5, 13, 1,4,1,-1);
yy(6, 13, 1,4,0,c3);
yy(7, 13, 1,4,1, -2);
yy(8, 13, 1,4,1,-1);
yy(9, 13, 1,4,1,-1);
yy(10, 13, 1,4,0,-1);
yy(11, 13, 1,4,0,-2);
yy(13, 13, 0,4,0,c5);
yy(12, 13, 1,4,1,-1);
yy(14, 13, 0,4,0,-a1*2);
yy(15, 13, 0,4,0,2);
yy(16, 13, 0,4,0,6);
yy(17, 13,0,4,0,2);
yy(18, 13, 0,4,0,2);
yy(19, 13, 0,3,1,0);
yy(20, 13, 0,2,1,0);


print("12:------");
yy(1, 12, 3,4,1, phi2);
yy(2, 12, 2,4,0,-phi2);
yy(3, 12, 3,4,1,1);
yy(4, 12,1,4,0,-d3)
yy(5, 12, 2,4,0,-1);
yy(6, 12, 2,4,1,-1);
yy(7, 12, 1,4,1, 0);
yy(8, 12, 1,4,1,1);
yy(9, 12, 1,4,1,1);
yy(10, 12, 1,4,0,1);
yy(11, 12, 1,4,0,0);
yy(13, 12, 2,4,0,-1);
yy(12, 12, 0,4,0,b(-3));
yy(14, 12, 0,4,0,0);
yy(15, 12, 1,4,0,2);
yy(16, 12, 0,4,0,0);
yy(17, 12,0,4,0,0);
yy(18, 12, 0,4,0,-4);
yy(19, 12, 0,3,1,0);
yy(20, 12, 0,4,0,-2);


print("14:------");
yy(1, 14, 3,4,2, phi2);
yy(2, 14, 3,4,1,a4);
yy(3, 14, 2,4,0,c6);
yy(4, 14,3,4,1,1)
yy(5, 14, 2,4,1,-1);
yy(6, 14, 1,4,0,d9);
yy(7, 14, 1,4,1, -a2);
yy(8, 14, 2,4,0,-1);
yy(9, 14, 1,4,1,-a3);
yy(10, 14, 3,4,0,1);
yy(11, 14, 1,4,0,-a5);
yy(13, 14, 1,4,0,-2*a1);
yy(12, 14, 0,4,0,0);
yy(14, 14, 0,4,0,a8);
yy(15, 14, 1,4,0,1);
yy(16, 14, 0,4,0,-12);
yy(17, 14,0,4,0,-2);
yy(18, 14, 0,4,0,0);
yy(19, 14, 0,3,1,0);
yy(20, 14, 0,4,0,0);


print("15:------");
yy(1, 15, 3,4,2, phi2);
yy(2, 15, 2,4,2,-1);
yy(3, 15, 2,4,0,c3);
yy(4, 15,1,4,1,b(1))
yy(5, 15, 2,4,1,-1);
yy(6, 15, 1,4,0,d7);
yy(7, 15, 2,4,1, -1);
yy(8, 15, 2,4,0,-a4);
yy(9, 15, 1,4,1,1);
yy(10, 15, 2,4,1,-1);
yy(11, 15, 1,4,0,1);
yy(13, 15, 1,4,0,2);
yy(12, 15, 1,4,1,2);
yy(14, 15, 1,4,0,1);
yy(15, 15, 0,4,0,a2);
yy(16, 15, 0,4,0,0);
yy(17, 15,0,4,0,-2);
yy(18, 15, 0,4,0,-4);
yy(19, 15, 0,3,1,0);
yy(20, 15, 0,4,0,0);


print("16:------");
y24(1, 16, 4,4,2, phi2);
y24(2, 16, 3,4,1,c10);
y24(3, 16, 3,4,0,c9);
y24(4, 16,3,4,1,a3)
y24(5, 16, 2,4,1,-a3);
y24(6, 16, 2,4,0,-a3*a7);
y24(7, 16, 2,4,1, 4);
y24(8, 16, 2,4,0,c11);
y24(9, 16, 2,4,1,-a6);
y24(10, 16, 1,4,0,-a3*a6);
y24(11, 16, 1,4,0,4*a3);
y24(13, 16, 2,4,0,6);
y24(12, 16, 1,4,1,0);
y24(14, 16, 1,4,0,-12);
y24(15, 16, 0,4,0,0);
y24(16, 16, 0,4,0,b(23));
y24(17, 16, 1,4,1,-1);
y24(18, 16, 1,4,1,1);
y24(19, 16, 1,4,1,1);
y24(20, 16, 1,4,1,-1);


print("17:------");
y4(1, 17, 4,4,2, phi2);
y4(2, 17, 3,4,1,c1);
y4(3, 17, 3,4,0,-a7);
y4(4, 17,3,4,1,-1)
y4(5, 17, 2,4,1,1);
y4(6, 17, 3,4,0,-a4);
y4(7, 17, 2,4,1, 2);
y4(8, 17, 3,4,1,-1);
y4(9, 17, 1,4,1,c4);
y4(10, 17, 2,4,0,1);
y4(11, 17, 1,4,0,-2);
y4(13, 17, 2,4,0,2);
y4(12, 17, 1,4,1,0);
y4(14, 17, 1,4,0,-2);
y4(15, 17, 1,4,0,-2);
y4(16, 17, 1,4,1,-1);
y4(17, 17, 0,4,0,b(3));
y4(18, 17, 1,4,1,-1);
y4(19, 17, 1,4,1,-1);
y4(20, 17, 1,4,1,1);

print("18:------");
y8(1, 18, 4,4,2, phi2);
y8(2, 18, 3,4,1,-phi2);
y8(3, 18, 4,4,0,a4);
y8(4, 18,2,4,1,c7)
y8(5, 18, 2,4,1,-a3);
y8(6, 18, 3,4,0,-a4);
y8(7, 18, 2,4,1, 0);
y8(8, 18, 2,4,0,-c3);
y8(9, 18, 2,4,2,1);
y8(10, 18, 1,4,1,a3);
y8(11, 18, 1,4,0,0);
y8(13, 18, 2,4,0,2);
y8(12, 18, 1,4,1,-4);
y8(14, 18, 1,4,0,0);
y8(15, 18, 1,4,0,-4);
y8(16, 18, 1,4,1,1);
y8(17, 18, 1,4,1,-1);
y8(18, 18, 0,4,0,b(7));
y8(19, 18, 1,4,1,1);
y8(20, 18, 1,4,1,-1);


print("19:------");
y3(1, 19, 4,4,2, phi2);
y3(2, 19, 3,4,2,-1);
y3(3, 19, 3,4,2,-1);
y3(4, 19,3,4,2,-1)
y3(5, 19, 2,4,2,1);
y3(6, 19, 2,4,1,1);
y3(7, 19,  2,4,1,1);
y3(8, 19,  2,4,1,1);
y3(9, 19, 2,4,1,1);
y3(10, 19,  1,4,1,-1);
y3(11, 19,  1,4,1,-1);
y3(13, 19, 2,4,0,0);
y3(12, 19, 1,4,1,0);
y3(14, 19, 1,4,0,0);
y3(15, 19, 1,4,0,0);
y3(16, 19,  1,4,1,1);
y3(17, 19, 1,4,1,-1);
y3(18, 19, 1,4,1,1)
y3(19, 19, 0,4,0,b(2));
y3(20, 19, 1,4,1,-1);


print("20:------");
y4(1, 20, 4,4,2, phi2);
y4(2, 20, 3,4,1,-phi2);
y4(3, 20, 3,4,1,-1);
y4(4, 20,2,4,2,1)
y4(5, 20, 2,4,1,1);
y4(6, 20, 2,4,1,1);
y4(7, 20,  2,4,1,0);
y4(8, 20,  2,4,2,1);
y4(9, 20, 1,4,1,-b(1));
y4(10, 20,  1,4,1,-1);
y4(11, 20,  1,4,1,0);
y4(13, 20, 2,4,0,0);
y4(12, 20, 1,4,1,-2);
y4(14, 20, 1,4,0,0);
y4(15, 20, 1,4,0,0);
y4(16, 20,  1,4,1,-1);
y4(17, 20, 1,4,1,1);
y4(18, 20, 1,4,1,-1)
y4(19, 20, 1,4,1,-1);
y4(20, 20, 0,4,0,b(3));

\\ KOT
\\1234567890 11 12 13 14 15 16 17 18 19 20 y
y(1, 12, 3, 4, 1, phi2/2);
y(2, 12, 2, 4, 0, -phi2/2);
y(3, 12, 3, 4, 1, 1/2);

print("---------");
y(3, 2, 1,0,0, c8);
