import os
import argparse
import numpy as np



parser = argparse.ArgumentParser(description='Argument parser')
parser.add_argument("--instances_path", help="Path where the instances are stored", required = True, type=str)
parser.add_argument("--file_name", help="Name of the file", required = True, type=str)
args = parser.parse_args()

def main():
	
	if not os.path.exists(args.instances_path + '/smt2_base'):
		os.makedirs(args.instances_path + '/smt2_base')
		
	file = open(args.instances_path + '/' + args.file_name,"r") 
	
	# Create the output file
	file_out = open(args.instances_path + '/smt2_base/'+ args.file_name[:-4] + "-out.smt2", "w+") 

	
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
	pieces = []
	for line in remaining_lines:
		line = line.split(" ")
		pieces.append([line[0],line[1]])
		
	
		
	file_out.write("; Variable declarations\n")
	
	file_out.write("(declare-fun w () Int)\n")
	file_out.write("(declare-fun h () Int)\n")
	file_out.write("(declare-fun n () Int)\n")
	
	# Declare all the shapes we can use as p_i_1, p_i_2 
	# (p_i_1 horizontal dimension of the i-th shape, p_i_2: vertical dimension of the i-th shape)
	for i in range(number_of_pieces):
		for j in range(2):
			file_out.write("(declare-fun p_{}_{} () Int)\n".format(i+1,j+1))
			
	# Declare all the origns of our pieces as o_i_1, o_i_2 
	# (o_i_1: horizontal coordinate of the origin of the i-th piece, o_i_2: vertical coordinate of the origin of the i-th piece)
	for i in range(number_of_pieces):
		for j in range(2):
			file_out.write("(declare-fun o_{}_{} () Int)\n".format(i+1,j+1))
			
	file_out.write("\n")
	
	
	# Initial assignmenent
	
	file_out.write("; Initial assignmenent\n")
	
	
	file_out.write("(assert (= w {}))\n".format(width))
	file_out.write("(assert (= h {}))\n".format(height))
	file_out.write("(assert (= n {}))\n".format(number_of_pieces))

	for i in range(number_of_pieces):
		for j in range(2):
			file_out.write("(assert (= p_{}_{} {}))\n".format(i+1,j+1,pieces[i][j]))
			
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
		file_out.write("(assert (and (<= (+ p_{i}_1 o_{i}_1 ) w) (<= (+ p_{i}_2 o_{i}_2 ) h) ))\n".format(i = i+1))
		
	file_out.write("\n")
	
	
	
	file_out.write("; Non-overlap\n")
	
	for i in range(number_of_pieces):
		for j in range(number_of_pieces):
			if (i<j):
				file_out.write("(assert (or (<= (+ o_{i}_1  p_{i}_1) o_{j}_1) (<= (+ o_{j}_1  p_{j}_1) o_{i}_1) (<= (+ o_{i}_2  p_{i}_2) o_{j}_2) (<= (+ o_{j}_2  p_{j}_2) o_{i}_2)))\n".format(i = i+1, j = j+1))

	file_out.write("\n")
	
	
	
	file_out.write("; Implied\n")
	
	for i in range(width):
		for j in range(number_of_pieces):
			file_out.write("(assert (<= (+  ")
			for t in range(number_of_pieces):
				file_out.write("(ite ( and (<= o_{t}_1 {i}) (< {i} (+ o_{t}_1 p_{t}_1))) p_{t}_2 0) ".format(i = i, t = t+1))
			file_out.write(") h))\n")
			
			
	for i in range(height):
		for j in range(number_of_pieces):	
			file_out.write("(assert (<= (+  ")
			for t in range(number_of_pieces):
				file_out.write("(ite ( and (<= o_{t}_2 {i}) (< {i} (+ o_{t}_2 p_{t}_2))) p_{t}_1 0) ".format(i = i, t = t+1))
			file_out.write(") w))\n")

	file_out.write("\n")
			
	
	
			
	file_out.write("; Solve\n")
	
	file_out.write("(check-sat)\n")
	
	file_out.write("(get-value (w))\n")
	file_out.write("(get-value (h))\n")
	file_out.write("(get-value (n))\n")
	
		
	
	for i in range(number_of_pieces):
		file_out.write("(get-value (p_{}_1))\n".format(i+1))
		file_out.write("(get-value (p_{}_2))\n".format(i+1))
		file_out.write("(get-value (o_{}_1))\n".format(i+1))
		file_out.write("(get-value (o_{}_2))\n".format(i+1))
	
	
	file.close() 
	file_out.close()
		
if __name__ == "__main__":
	main()