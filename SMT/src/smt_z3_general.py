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

	
	i = 0
	for line in remaining_lines:
		couple = line.replace(" ", "").strip()
		size = line.split(" ")
		if size[0] != size[1]:
			pieces.append([[int(size[0]),int(size[1])], [int(size[1]),int(size[0])]])
		else:
			pieces.append([[int(size[0]),int(size[1])], [-1,-1]])
		i+=1
		couples[couple] = couples.get(couple,0) + 1
		
	ncopy = list(couples.values())
	number_of_different_pieces = np.array([ncopy]).size
	
	
	
	# Variables
	
	O = [ [ Int("o_{}_{}".format(i+1, j+1)) for j in range(2) ]
	for i in range(number_of_pieces) ]
	
	P = [ [ Int("p_{}_{}".format(i+1, j+1)) for j in range(2) ]
	for i in range(number_of_pieces) ]
	
	
	
	# Constraints
	
	rotation = [Or(And(P[i][x] == pieces[i][0][x], P[i][y] == pieces[i][0][y]), And(P[i][x] == pieces[i][1][x], P[i][y] == pieces[i][1][y], P[i][x] != -1) ) for i in range(number_of_pieces)]
	
	in_domain = [ And(O[i][x] >= 0, O[i][x] < width, O[i][y] >= 0, O[i][y] < height) for i in range(number_of_pieces)] 
		
	
	# pieces fit in the rectangle
	in_paper = [ And(P[i][x] + O[i][x] <= width, P[i][y] + O[i][y] <= height ) for i in range(number_of_pieces)] 
		
	# non-overlapping
	no_overlap = []		
	for i in range(number_of_pieces):
		for j in range(number_of_pieces):
			if (i<j):
				no_overlap.append(Or(O[i][x]+ P[i][x]  <= O[j][x], O[j][x]+ P[j][x]<= O[i][x], O[i][y]+ P[i][y]  <= O[j][y], O[j][y] + P[j][y] <= O[i][y]))
				
	
	implied = []
	for i in range(width):
		for j in range(number_of_pieces):
			implied.append(Sum([If(And(O[j][x] <= i, i < O[j][x] + P[j][x]), P[j][y],0) for j in range(number_of_pieces)]) <= height)
	
	for i in range(height):
		for j in range(number_of_pieces):
			implied.append(Sum([If(And( O[j][y] <= i, i < O[j][y] + P[j][y]), P[j][x],0) for j in range(number_of_pieces)]) <= width)
					
  
					
	
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
	
				
	constraints = in_domain + rotation + in_paper + no_overlap + order 
	
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
			print("{:<1} {:<3} {:<1} {:<2}".format(str(m[P[i][x]]),str(m[P[i][y]]), str(m[O[i][x]]), str(m[O[i][y]])))
			file_out.write("{:<1} {:<3} {:<1} {:<2}\n".format(str(m[P[i][x]]), str(m[P[i][y]]), str(m[O[i][x]]), str(m[O[i][y]])))
			color = ["#"+''.join([random.choice('0123456789ABCDEF') for j in range(6)])]
			sq = Rectangle(( m[O[i][x]].as_long(),  m[O[i][y]].as_long()),m[P[i][x]].as_long(),m[P[i][y]].as_long(),fill = True,color=color[0], alpha=.3 )
			ax.add_patch(sq)
				
		#print("\n{}\n".format(s.statistics()))
		
		plt.plot()
		plt.show()
		
	else: print("Failed to solve")
	
	file.close() 
	file_out.close()
		
if __name__ == "__main__":
	main()