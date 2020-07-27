import os
import argparse
import numpy as np
import matplotlib.pyplot as plt
import random
from matplotlib.patches import Rectangle
from z3 import *


parser = argparse.ArgumentParser(description='Argument parser')
parser.add_argument("--instances_path", help="Path where the instances are stored", required = True, type=str)
parser.add_argument("--file_name", help="Name of the file", required = True, type=str)
args = parser.parse_args()

def main():
	
	if not os.path.exists(args.instances_path + '/out_general'):
		os.makedirs(args.instances_path + '/out_general')
		
	file = open(args.instances_path + '/' + args.file_name,"r") 
	
	# Create the output file
	file_out = open(args.instances_path + '/out_general/'+ args.file_name[:-4] + "-out.txt", "w+") 
	
	x = 0
	y = 1
	
	# Initial and derivided data
	
	# Read the first line which contains the width and the height of the paper roll
	first_line = file.readline().strip().split(" ")
	
	width = int(first_line[0])
	height = int(first_line[1])

	# Read the second line which contains the number of necessary pieces of paper to cut off
	second_line = file.readline().strip().split(" ")
	
	number_of_pieces = int(second_line[0])
	
	# Read all the remaining lines which contains the horizontal and vertical dimensionof the i-th piece of paper
	remaining_lines = file.readlines()
	
	# To remove empty lines
	remaining_lines = [line.strip() for line in remaining_lines if line.strip()]
	
	
	couples = {}
	pieces = []
	shape = []

	
	i = 0
	number_of_shapes = 0
	for line in remaining_lines:
		couple = line.replace(" ", "").strip()
		size = line.split(" ")
		if size[0] != size[1]:
			pieces.append([int(size[0]),int(size[1])])
			pieces.append([int(size[1]),int(size[0])])
			shape.append([number_of_shapes,number_of_shapes+1])
			number_of_shapes += 2
			i+=1
		else:
			pieces.append([int(size[0]),int(size[1])])
			shape.append([number_of_shapes,-1])
			number_of_shapes += 1
			i+=1
		couples[couple] = couples.get(couple,0) + 1
		
	ncopy = list(couples.values())
	number_of_different_pieces = np.array([ncopy]).size
	
	
	
	# Variables
	
	O = [ [ Int("o_{}_{}".format(i+1, j+1)) for j in range(2) ]
	for i in range(number_of_pieces) ]
	
	#R = [ Int("r_{}".format(i+1)) for i in range(number_of_pieces) ]
	R = [ Bool("r_{}".format(i+1)) for i in range(number_of_pieces) ]
			
	
	# Constraints
	
	in_domain = [ And (O[i][x] >= 0, O[i][x] < width, O[i][y] >= 0, O[i][y] < height) for i in range(number_of_pieces)] 
	
	disallow_config = []
	for i in range(number_of_pieces):
			disallow_config.append(If(R[i], shape[i][0], shape[i][1]) != -1)
	
	
	
	in_paper = []
	for i in range(number_of_pieces):
		for r in range(number_of_shapes):
			in_paper.append(Implies(r == If(R[i], shape[i][0], shape[i][1]),And(pieces[r][x] + O[i][x] <= width, pieces[r][y] + O[i][y] <= height )))
	

	
	no_overlap = []		
	for i in range(number_of_pieces):
		for j in range(number_of_pieces):
			if (i<j):
				for r1 in range(number_of_shapes):
					for r2 in range(number_of_shapes):
						no_overlap.append(Implies(And(r1 == If(R[i], shape[i][0], shape[i][1]),r2 == If(R[j], shape[j][0], shape[j][1])),
						Or(O[i][x]+ pieces[r1][x]  <= O[j][x], O[j][x]+ pieces[r2][x]<= O[i][x], O[i][y]+ pieces[r1][y]  <= O[j][y], O[j][y] + pieces[r2][y] <= O[i][y])))
					
  
					
	
	base = []
	for i in range(number_of_different_pieces):
		if i == 0:
			base.append(0)
		else:
			base.append(sum(ncopy[0:i]))
							
	order = []
	for i in range(number_of_different_pieces):
		for j in range(ncopy[i]-1):
			order.append(And(O[base[i]+j][x] >= O[base[i]+j+1][x], Implies(O[base[i]+j][x] == O[base[i]+j+1][x],O[base[i]+j][y] >= O[base[i]+j+1][y])))
	
				
	constraints = in_domain + disallow_config + in_paper + no_overlap + order 
	
	
	# Create the solver
	s = Solver()
	s.add(constraints)
	fig = plt.figure(figsize=(5 + (width//8) ,5 + (height//8)))
	ax = fig.gca(title = "Plot of the solution")
	
	if s.check() == sat:
	
		m = s.model()
		
		print("{} {}".format(height, width))
		file_out.write("{} {}\n".format(height,width))
		
		print("{}".format(number_of_pieces))
		file_out.write("{}\n".format(number_of_pieces))

		for i in range(number_of_pieces):
			if bool(m[R[i]]):
				result = shape[i][0]
			else:
				result = shape[i][1]
			print("{:<1} {:<3} {:<1} {:<2}".format(pieces[result][x], pieces[result][y], str(m[O[i][x]]), str(m[O[i][y]])))
			file_out.write("{:<1} {:<3} {:<1} {:<2}\n".format(pieces[result][x], pieces[result][y], str(m[O[i][x]]), str(m[O[i][y]])))
			color = ["#"+''.join([random.choice('0123456789ABCDEF') for j in range(6)])]
			sq = Rectangle(( m[O[i][x]].as_long(),  m[O[i][y]].as_long()),pieces[result][x],pieces[result][y],fill = True,color=color[0], alpha=.3 )
			ax.add_patch(sq)
				
		#print("\n{}\n".format(s.statistics()))
		
		plt.plot()
		plt.show()
		
	else: print("Failed to solve")
	
	file.close() 
	file_out.close()
		
if __name__ == "__main__":
	main()