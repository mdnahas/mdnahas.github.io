#! /usr/bin/env python3

# Reorganized version of solve.py, so that I can write solve3


import sys

import numpy as np


POINTS_FOR_TD = 7

# Number of first downs between the goal lines.
### WARNING - THIS CAN BE CHANGED
FIELD_LENGTH = 9

# The vector layout is:
# 0: expected points when home possesses ball and is 1 first down from TD
# 1: ... home ... 2 first downs from TD
# ...
# FIELD_LENGTH - 1: ... home ... FIELD_LENGTH first downs from TD
# FIELD_LENGTH: ... away ... FIELD_LENGTH first down from TD
# FIELD_LENGTH + 1: ... away ... FIELD_LENGTH - 1 first downs from TD
# ...
# 2*FIELD_LENGTH - 1: ... away ... 1 first downs from TD
# 2*FIELD_LENGTH: constant value of 1

# Helper functions to index into vector (or matrix)
# This use a global variable, which is bad form.
# (But I didn't want to pass it to everything).
def const_index():
    return 2*FIELD_LENGTH
def home_index(fd_to_go):
    return fd_to_go-1
def away_index(fd_to_go):
    return 2*FIELD_LENGTH - fd_to_go
def switch_ends(fd_to_go):
    return FIELD_LENGTH - (fd_to_go-1)
    

# Takes first down probability for home and away teams.
# Returns a vector with expected points at each place on field
def solve_for_expected_points(fdp_home, fdp_away):
    # create matrix with zeros
    matrix = np.zeros(( 2*FIELD_LENGTH + 1, 2*FIELD_LENGTH + 1))

    # copy constant value 1 from input to output
    matrix[const_index(), const_index()] = 1.0

    # home is 1 first down from TD
    # positive points for touchdown
    matrix[home_index(1), const_index()] = fdp_home * POINTS_FOR_TD 
    #matrix[home_index(1), away_index(FIELD_LENGTH-3)] = fdp_home
    matrix[home_index(1), away_index(switch_ends(1))] = (1.0 - fdp_home) 


    # away is 1 first down from TD
    # negative points for opposing team TD
    matrix[away_index(1), const_index()] = fdp_away * -POINTS_FOR_TD
    #matrix[away_index(1), home_index(FIELD_LENGTH-3)] = fdp_away
    matrix[away_index(1), home_index(switch_ends(1))] = (1-fdp_away)

    for i in range(0, FIELD_LENGTH-1):
        # home
        matrix[home_index(2+i), home_index(1+i)] = fdp_home
        matrix[home_index(2+i), away_index(switch_ends(2+i))] = (1.0 - fdp_home) 
        # away
        matrix[away_index(2+i), away_index(1+i)] = fdp_away
        matrix[away_index(2+i), home_index(switch_ends(2+i))] = (1.0 - fdp_away) 

    print(matrix)
    
    # Calculate eigenvalues and eigenvectors
    eigenvalues, eigenvectors = np.linalg.eig(matrix)

    # Find eigenvectors with eigenvalues equal to 1
    eigenvectors_with_1 = []
    for i in range(len(eigenvalues)):
        if np.isclose(eigenvalues[i], 1.0):
            eigenvectors_with_1.append(eigenvectors[:, i])

    if len(eigenvectors_with_1) != 1:
        print("ERROR: Eigenvalue not unique.  There were " + str(len(eigenvectors_with_1)) + " copies!")
        exit(1)

    return eigenvectors_with_1[0]
            

def main():
    global FIELD_LENGTH  # Declare that I may assign a global variable.
    
    if len(sys.argv) != 3 and len(sys.argv) != 4:
        print("Needs two first down probabilities", file=sys.stderr)
        sys.exit(1)

    # read in args with first down probabilities for home and away teams
    fdp_home = float(sys.argv[1])
    fdp_away = float(sys.argv[2])
    if len(sys.argv) == 4:
        # THIS OVERWRITES A GLOBAL VARIABLE -- UGLY!
        FIELD_LENGTH = int(sys.argv[3])
    
    eigenvector = solve_for_expected_points(fdp_home, fdp_away)

    should_be_1 = eigenvector[const_index()]
    scaled_eigenvector = (1.0 / should_be_1) * eigenvector
    #print(scaled_eigenvector)
    
    print("Firstdowns to Home TD,\tEP for Home with Home possession,\tEP for Home with Away possession")
    for i in range(0, FIELD_LENGTH):
        print(str(i+1) + ",\t" + str(scaled_eigenvector[home_index(i+1)].real) + ",\t" + str(scaled_eigenvector[away_index(switch_ends(i+1))].real))

    print("Test for linearity")
    first_diff = scaled_eigenvector[home_index(1)].real - scaled_eigenvector[home_index(2)].real
    max_diff = 0.0
    for i in range(0, FIELD_LENGTH-1):
        max_diff = max(max_diff, abs(scaled_eigenvector[home_index(i+1)].real - scaled_eigenvector[home_index(i+2)].real - first_diff))
    print("   max deviation from linearity: " + str(max_diff))

    
if __name__ == "__main__":
    # execute only if run as a script
    main()


