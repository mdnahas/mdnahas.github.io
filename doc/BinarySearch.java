
class BinarySearch {
    public static int binarySearch1(int[] A, int V) {
	int L = 0;
	int U = A.length;
	while (U-L > 0) {
	    int M = L + ((U-L)/2);
	    if (A[M] == V) 
		return M;
	    else if (V < A[M]) 
		U = M;
	    else
		L = M+1;
	}
	return -1;
    }

    public static int binarySearch2(int A[], int V) {
	int L = 0;
	int U = A.length;
	while (U-L > 0) {
	    int M = L + ((U-L)/ 2);
	    System.out.println("L=" + L + "   M=" + M + "  U=" + U);
	    if (A[M] < V)
		L = M+1;
	    else
		U = M;
	}
	return U;
    }

    public static void main(String[] args) {
	int[] A = {0,2,4,6,8};

	System.out.println("Algo1");
	for (int i = -1; i < 10; i++) {
	    System.out.println("search " + i + " yields " + binarySearch1(A, i));
	}

	System.out.println("Algo2");
	for (int i = -1; i < 10; i++) {
	    System.out.println("search " + i + " yields " + binarySearch2(A, i));
	}


	System.out.println("Algo2 - B");
	int[] B = {0,0,0,0,0};
	System.out.println("search " + -1 + " yields " + binarySearch2(B, -1));
	System.out.println("search " +  0 + " yields " + binarySearch2(B,  0));
	System.out.println("search " +  1 + " yields " + binarySearch2(B,  1));
	
    }
    
    
}
