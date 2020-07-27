import os
import os.path
import sys
import argparse
import glob
import numpy as np

parser = argparse.ArgumentParser(description='Argument parser')
parser.add_argument("--instances_path", help="Path of the directory where are stored the files to be converted", required = True, type=str)
parser.add_argument("--target_conversion", help="You can choose which dzn file you want to create, for the base model for the general model of for both", choices=['both', 'base', 'general'], default = "both", type=str)
args = parser.parse_args()

def main():
	"""Main converter function."""
	
	if args.target_conversion == "both":
		if not os.path.exists(args.instances_path + '/dzn_base'):
			os.makedirs(args.instances_path + '/dzn_base')

		if not os.path.exists(args.instances_path + '/dzn_general'):
			os.makedirs(args.instances_path + '/dzn_general')
	elif args.target_conversion == "base":
		if not os.path.exists(args.instances_path + '/dzn_base'):
			os.makedirs(args.instances_path + '/dzn_base')
	else:
		if not os.path.exists(args.instances_path + '/dzn_general'):
			os.makedirs(args.instances_path + '/dzn_general')


		
	# List of all the file to be converted	
	file_list = [f for f in glob.glob(args.instances_path + "/*.txt")]
	
	for file in file_list:
		# Open the txt file
		file_txt = open(file,"r") 
		
		file_name = os.path.basename(file)
		file_name = os.path.splitext(file_name)[0]
		
		if args.target_conversion == "both":
			# Create a dzn file for the base case
			file_dzn_base = open(args.instances_path + '/dzn_base/' + file_name + ".dzn", "w+") 
			
			# Create a dzn file for the "rotation" case (points 5,6)
			file_dzn_general = open(args.instances_path + '/dzn_general/' + file_name + ".dzn", "w+") 
			
			# Read the first line which contains the width and the height of the paper roll
			first_line = file_txt.readline().strip().split(" ")
			
			# Write it in the form of:
			# h = height of the paper roll; 
			# w = width of the paper roll;
			file_dzn_base.write("w = " + first_line[0] + ";\n")
			file_dzn_base.write("h = " + first_line[1] + ";\n")
			
			file_dzn_general.write("w = " + first_line[0] + ";\n")
			file_dzn_general.write("h = " + first_line[1] + ";\n")
			
			# Read the second line which contains the number of pieces of paper to cut off
			second_line = file_txt.readline().strip().split(" ")
			
			# Write it in the form of n = n;
			file_dzn_base.write("n = " + second_line[0] + ";\n")
			
			file_dzn_general.write("n = " + second_line[0] + ";\n")
			
			# Read all the remaining lines which contains the horizontal and vertical dimensionof the i-th piece of paper
			remaining_lines = file_txt.readlines()
			
			# To remove empty lines
			remaining_lines = [line.strip() for line in remaining_lines if line.strip()]	
			
			# Processing of the remaining lines
			dimensions = "dimension = ["
			
			rect_dimension = "rect_dimension = ["
			rect_offset = "rect_offset = ["
			shape = "shape = ["
			shapeind = "shapeind = ["
			i = 1
			
			ncopy = "ncopy = "
			couples = {}
			
			for line in remaining_lines:
				couple = line.replace(" ", "").strip()
				dimension = line.split(" ")
				if dimension[0] != dimension[1]:
					rect_dimension += "|\n" + dimension[0] + ", " + dimension[1] 
					rect_offset += "|\n" + str(0) + ", " + str(0)
					shape += "{" + str(i) + "}" + ", "
					shapeind += "{" + str(i) + ", "
					i+=1
					rect_dimension += "|\n" + dimension[1] + ", " + dimension[0]
					rect_offset += "|\n" + str(0) + ", " + str(0)
					shape += "{" + str(i) + "}" + ", "
					shapeind += str(i) + "}, "
					i+=1
				else:
					rect_dimension += "|\n" + dimension[0] + ", " + dimension[1] 
					rect_offset += "|\n" + str(0) + ", " + str(0)
					shape += "{" + str(i) + "}" + ", "
					shapeind += "{" + str(i) + "}, "
					i+=1
				dimensions += "|\n" + dimension[0] + ", " + dimension[1] 
				couples[couple] = couples.get(couple,0) + 1
			
			dimensions += "|];\n"
			
			i -= 1
			rect_dimension += "|];\n"
			rect_offset += "|];\n"
			shape = shape[:-2]
			shape += "];\n"
			shapeind = shapeind[:-2]
			shapeind += "];\n"
			
			ncopy += str(str(list(couples.values()))) + ";\n"
			
			# Write the necessary data in each file		
			file_dzn_base.write(dimensions)
			
			file_dzn_general.write("m = " + str(i) + ";\n")
			file_dzn_general.write(rect_dimension)
			file_dzn_general.write(rect_offset)
			file_dzn_general.write(shape)
			file_dzn_general.write(shapeind)
			file_dzn_general.write(ncopy)
			file_dzn_general.write("c = " + str(np.array([list(couples.values())]).size) + ";\n")
			
			# Close the files
			file_txt.close() 
			file_dzn_base.close()
			file_dzn_general.close() 
		
		elif args.target_conversion == "base":
		
			# Create a dzn file for the base case
			file_dzn_base = open(args.instances_path + '/dzn_base/' + file_name + ".dzn", "w+") 
			
			# Read the first line which contains the width and the height of the paper roll
			first_line = file_txt.readline().strip().split(" ")
			
			# Write it in the form of:
			# h = height of the paper roll; 
			# w = width of the paper roll;
			file_dzn_base.write("w = " + first_line[0] + ";\n")
			file_dzn_base.write("h = " + first_line[1] + ";\n")
			
			
			# Read the second line which contains the number of pieces of paper to cut off
			second_line = file_txt.readline().strip().split(" ")
			
			# Write it in the form of n = n;
			file_dzn_base.write("n = " + second_line[0] + ";\n")
			
			
			# Read all the remaining lines which contains the horizontal and vertical dimensionof the i-th piece of paper
			remaining_lines = file_txt.readlines()
			
			# To remove empty lines
			remaining_lines = [line.strip() for line in remaining_lines if line.strip()]	
			
			# Processing of the remaining lines
			dimensions = "dimension = ["
			
			
			for line in remaining_lines:
				dimension = line.split(" ")
				dimensions += "|\n" + dimension[0] + ", " + dimension[1] 
			
			dimensions += "|];\n"
				
			file_dzn_base.write(dimensions)
			
			# Close the files
			file_txt.close() 
			file_dzn_base.close()
			
		else:
			
			# Create a dzn file for the "rotation" case (points 5,6)
			file_dzn_general = open(args.instances_path + '/dzn_general/' + file_name + ".dzn", "w+") 
			
			# Read the first line which contains the width and the height of the paper roll
			first_line = file_txt.readline().strip().split(" ")
			
			# Write it in the form of:
			# h = height of the paper roll; 
			# w = width of the paper roll;			
			file_dzn_general.write("w = " + first_line[0] + ";\n")
			file_dzn_general.write("h = " + first_line[1] + ";\n")
			
			# Read the second line which contains the number of pieces of paper to cut off
			second_line = file_txt.readline().strip().split(" ")
			
			# Write it in the form of n = n;
			file_dzn_general.write("n = " + second_line[0] + ";\n")
			
			# Read all the remaining lines which contains the horizontal and vertical dimensionof the i-th piece of paper
			remaining_lines = file_txt.readlines()
			
			# To remove empty lines
			remaining_lines = [line.strip() for line in remaining_lines if line.strip()]	
			
			# Processing of the remaining lines
			rect_dimension = "rect_dimension = ["
			rect_offset = "rect_offset = ["
			shape = "shape = ["
			shapeind = "shapeind = ["
			i = 1
			
			ncopy = "ncopy = "
			couples = {}
			
			for line in remaining_lines:
				couple = line.replace(" ", "").strip()
				dimension = line.split(" ")
				if dimension[0] != dimension[1]:
					rect_dimension += "|\n" + dimension[0] + ", " + dimension[1] 
					rect_offset += "|\n" + str(0) + ", " + str(0)
					shape += "{" + str(i) + "}" + ", "
					shapeind += "{" + str(i) + ", "
					i+=1
					rect_dimension += "|\n" + dimension[1] + ", " + dimension[0]
					rect_offset += "|\n" + str(0) + ", " + str(0)
					shape += "{" + str(i) + "}" + ", "
					shapeind += str(i) + "}, "
					i+=1
				else:
					rect_dimension += "|\n" + dimension[0] + ", " + dimension[1] 
					rect_offset += "|\n" + str(0) + ", " + str(0)
					shape += "{" + str(i) + "}" + ", "
					shapeind += "{" + str(i) + "}, "
					i+=1
				couples[couple] = couples.get(couple,0) + 1
			
			
			i -= 1
			rect_dimension += "|];\n"
			rect_offset += "|];\n"
			shape = shape[:-2]
			shape += "];\n"
			shapeind = shapeind[:-2]
			shapeind += "];\n"
			ncopy += str(str(list(couples.values()))) + ";\n"
			
			file_dzn_general.write("m = " + str(i) + ";\n")
			file_dzn_general.write(rect_dimension)
			file_dzn_general.write(rect_offset)
			file_dzn_general.write(shape)
			file_dzn_general.write(shapeind)
			file_dzn_general.write(ncopy)
			file_dzn_general.write("c = " + str(np.array([list(couples.values())]).size) + ";\n")
			
			# Close the files
			file_txt.close() 
			file_dzn_general.close() 

	


if __name__ == "__main__":
	main()