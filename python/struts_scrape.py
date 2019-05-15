import urllib2
import re
import os
import errno

url = "http://localhost:8080/struts2-showcase-2_5_20/"
#connect to a URL

def get_links(url):

	website = urllib2.urlopen(url)

	#read html code
	html = website.read()

	#use re.findall to get all the links
	links = re.findall('href=.*.action', html)

	links.extend([x[:x.find("jsp") + 3] for x in re.findall('href=.*.jsp', html)])
	links.extend([x[:x.find(";")] for x in re.findall("href=.*;", html)])

	return links





links = get_links(url)


for link in links:

	if "viewSource" in link:
		continue

	elif  "#\">&times" in link:
		continue



	path = link[len("href=\""):]
	print path


	try:
		url = "http://localhost:8080" + path
		website = urllib2.urlopen(url)
		#read html code
		html = website.read()

		#use re.findall to get all the links
		form_data = re.findall("<input[^>]*", html)

		form_data_set = set(form_data)


		if len(form_data_set) > 0:
			dict_name = "/home/jamesk/Documents/CS_701/jqf/examples/src/test/resources/dictionaries" + path.replace("!", "_") + "body_vals.dict"

			if not os.path.exists(os.path.dirname(dict_name)):
				try:
					os.makedirs(os.path.dirname(dict_name))
				except OSError as exc: # Guard against race condition
					if exc.errno != errno.EEXIST:
			    			raise

	# 		f = open(dict_name, "w")
	# 		for d in form_data_set:
	# 			if d.find("hidden") > 0:
	# 				continue
	# 			if d.find("name=\"") <=0:
	# 				continue
	# 			d = d[d.find("name=\"") + len("name=\""):  ]
	# 			d = d[:d.find("\"")]
	# 			f.write(d + "\n")

	# 		f.close()
	# except:
		continue
	
