import os
import argparse
import numpy as np


parser = argparse.ArgumentParser(description='Argument parser')
parser.add_argument("--instances_path", help="Path where the instances are stored", required = True, type=str)
parser.add_argument("--file_name", help="Name of the file", required = True, type=str)
args = parser.parse_args()

def main():
	
	if not os.path.exists(args.instances_path + '/smt2_general'):
		os.makedirs(args.instances_path + '/smt2_general')
		
	file = open(args.instances_path + '/' + args.file_name,"r") 
	
	# Create the output file
	file_out = open(args.instances_path + '/smt2_general/'+ args.file_name[:-4] + "-out.smt2", "w+") 
	
	
	# Read the first line which contains the width and the height of the paper roll
	first_line = file.readline().strip().split(" ")
	
	height = int(first_line[0])
	width = int(first_line[1])

	# Read the second line which contains the number of necessary pieces of paper to cut off
	second_line = file.readline().strip().split(" ")
	
	number_of_pieces = int(second_line[0])
	
	# Read all the remaining lines which contains the horizontal and vertical dimensionof of each piece of paper
	remaining_lines = file.readlines()
	# To remove empty lines
	remaining_lines = [line.strip() for line in remaining_lines if line.strip()]
	
	# Extract all the data we need from the input instance	
	couples = {}
	pieces = []
	shape = []

	i = 0
	number_of_rectangles = 0
	for line in remaining_lines:
		couple = line.replace(" ", "").strip()
		size = line.split(" ")
		if size[0] != size[1]:
			pieces.append([int(size[0]),int(size[1])])
			pieces.append([int(size[1]),int(size[0])])
			shape.append([number_of_rectangles,number_of_rectangles+1])
			number_of_rectangles += 2
			i+=1
		else:
			pieces.append([int(size[0]),int(size[1])])
			shape.append([number_of_rectangles,-1])
			number_of_rectangles += 1
			i+=1
		couples[couple] = couples.get(couple,0) + 1
		
	
	ncopy = list(couples.values())
	number_of_different_rectangles = np.array([ncopy]).size
	
	base = []
	for i in range(number_of_different_rectangles):
		if i == 0:
			base.append(0)
		else:
			base.append(sum(ncopy[0:i]))
			
	
	
	file_out.write("; Variable declarations\n")
	
	file_out.write("(declare-fun w () Int)\n")
	file_out.write("(declare-fun h () Int)\n")
	file_out.write("(declare-fun n () Int)\n")
	
	# Declare all the shapes we can use as p_i_1, p_i_2 
	# (p_i_1 horizontal dimension of the i-th shape, p_i_2: vertical dimension of the i-th shape)
	for i in range(number_of_rectangles):
		for j in range(2):
			file_out.write("(declare-fun p_{}_{} () Int)\n".format(i+1,j+1))
			
	# Declare all the shape variables that contains for each piece its possible rotation 
	# (s_1_1 contains the first possible rotation of the first piece, s_1_2 contains the other possible rotation of the first piece)
	for i in range(number_of_pieces):
		for j in range(2):
			file_out.write("(declare-fun s_{}_{} () Int)\n".format(i+1,j+1))
	
	# Declare all the origns of our pieces as o_i_1, o_i_2 
	# (o_i_1: horizontal coordinate of the origin of the i-th piece, o_i_2: vertical coordinate of the origin of the i-th piece)
	for i in range(number_of_pieces):
		for j in range(2):
			file_out.write("(declare-fun o_{}_{} () Int)\n".format(i+1,j+1))
	
	# Declare all the rotation of our pieces	
	for i in range(number_of_pieces):
		file_out.write("(declare-fun r_{} () Int)\n".format(i+1))
			
	file_out.write("\n")
	
	
	# Initial assignmenent
	
	file_out.write("; Initial assignmenent\n")
	
	
	file_out.write("(assert (= w {}))\n".format(width))
	file_out.write("(assert (= h {}))\n".format(height))
	file_out.write("(assert (= n {}))\n".format(number_of_pieces))

	for i in range(number_of_rectangles):
		for j in range(2):
			file_out.write("(assert (= p_{}_{} {}))\n".format(i+1,j+1,pieces[i][j]))
			
	for i in range(number_of_pieces):
		for j in range(2):
			file_out.write("(assert (= s_{}_{} {}))\n".format(i+1,j+1,shape[i][j]))
			
	file_out.write("\n")
			
	
	# Constraints
	
	file_out.write("; Constraints\n")
	file_out.write("\n")
	
	
	file_out.write("; Origins domain\n")

	for i in range(number_of_pieces):
		file_out.write("(assert (and (>= o_{i}_1 0) (< o_{i}_1 w)  (>= o_{i}_2 0)  (< o_{i}_2 h)))\n".format(i = i+1))
		
	file_out.write("\n")
	
	
		
	
	file_out.write("; Pieces fit in the paper\n")

	for i in range(number_of_pieces):
		for r in range(number_of_rectangles):
			file_out.write("(assert (implies (= {r} (ite (= r_{i} 0) s_{i}_1 s_{i}_2)) (and (<= (+ p_{r_index}_1 o_{i}_1) w) (<= (+ p_{r_index}_2 o_{i}_2) h))))".format(i = i+1, r = r, r_index = r+1))
		
	file_out.write("\n")
	

	
	file_out.write("; Disallow config\n")
	
	for i in range(number_of_pieces):
		file_out.write("(assert ( not ( = (ite (= r_{i} 0) s_{i}_1 s_{i}_2) -1)))\n".format(i = i+1))
	
	file_out.write("\n")
	
	
	
	file_out.write("; Non-overlap\n")

	for i in range(number_of_pieces):
		for j in range(number_of_pieces):
			if (i<j):
				for r1 in range(number_of_rectangles):
					for r2 in range(number_of_rectangles):
						file_out.write("(assert (implies (and (= {r1} (ite (= r_{i} 0) s_{i}_1 s_{i}_2)) (= {r2} (ite (= r_{j} 0) s_{j}_1 s_{j}_2))) (or (<=(+ o_{i}_1 p_{r1_index}_1) o_{j}_1) (<=(+ o_{j}_1 p_{r2_index}_1) o_{i}_1) (<=(+ o_{i}_2 p_{r1_index}_2) o_{j}_2) (<=(+ o_{j}_2 p_{r2_index}_2) o_{i}_2) ) ))".format(i = i+1, j = j+1, r1 = r1, r2 = r2, r1_index = r1+1, r2_index = r2+1))

	file_out.write("\n")
	
	

	
	file_out.write("; Rotation domain\n")
	
	for i in range(number_of_pieces):
		file_out.write("(assert (and (>= r_{i} 0) (< r_{i} 2)))\n".format(i = i+1))
	
	file_out.write("\n")
	
	
	
	file_out.write("; Order\n")
	
	for i in range(number_of_different_rectangles):
		for j in range(ncopy[i]-1):
			file_out.write("(assert( and (>= o_{this}_1 o_{next}_1) (implies (= o_{this}_1 o_{next}_1) (>= o_{this}_2 o_{next}_2))))\n".format(this = base[i]+j+1, next = base[i]+j+2))

	file_out.write("\n")
	
	
			
	file_out.write("; Solve\n")
	file_out.write("(check-sat)\n")
	
	file_out.write("(get-value (w))\n")
	file_out.write("(get-value (h))\n")
	file_out.write("(get-value (n))\n")

	
	for i in range(number_of_pieces):
		file_out.write("(get-value (r_{}))\n".format(i+1))
		file_out.write("\n")
		file_out.write("(get-value (p_{}_1))\n".format(shape[i][0]+1))
		file_out.write("(get-value (p_{}_2))\n".format(shape[i][0]+1))
		if shape[i][1] != -1:
			file_out.write("\n")
			file_out.write("(get-value (p_{}_1))\n".format(shape[i][1]+1))
			file_out.write("(get-value (p_{}_2))\n".format(shape[i][1]+1))
		file_out.write("\n")
		file_out.write("(get-value (o_{}_1))\n".format(i+1))
		file_out.write("(get-value (o_{}_2))\n".format(i+1))
	
	
	
	file.close() 
	file_out.close()
		
if __name__ == "__main__":
	main()