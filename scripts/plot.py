#!/usr/bin/env python2

import csv
import sys
import numpy as np

import math

import matplotlib
#matplotlib.use('pdf')
from matplotlib.backends.backend_pdf import PdfPages
import matplotlib.pyplot as plt
import matplotlib.ticker as ticker

from os.path import split

conf = [
    {
        'title': 'Total Paths',
        'col': ' paths_total',
        'type': int,
        'format': '%d',
    },
    {
        'title': 'Unique Crashes',
        'col': ' unique_crashes',
        'type': int,
        'format': '%d',
    },
    {
        'title': 'Valid Inputs',
        'col': ' valid_inputs',
        'type': int,
        'format': '%d',
    },
    {
        'title': 'Invalid Inputs',
        'col': ' invalid_inputs',
        'type': int,
        'format': '%d',
    },
    {
        'title': 'Coverage (%)',
        'col': ' map_size',
        'type': float,
        'format': '%0.1f',
    },
    {
        'title': 'Valid Coverage (%)',
        'col': ' valid_cov',
        'type': float,
        'format': '%0.1f',
    },
]



with PdfPages('fig.pdf') as pdf:
    for c in conf:
        #fig = plt.figure()
        fig, ax = plt.subplots()
        ymax = 0

        for arg in sys.argv[1:]:

            # List to hold x values.
            x_number_values = []

            # List to hold y values.
            y_number_values = []

            t0 = None;

            with open(arg) as csvfile:
                reader = csv.DictReader(csvfile, delimiter=',')
                for line in reader:
                    y_number_values.append(float(line[c['col']].replace('%','')))
                    if t0 is None:
                        t0 = int(line['# unix_time'])
                    t = int(line['# unix_time'])
                    x_number_values.append(t - t0)

            ymax = max(ymax, y_number_values[-1])
            # Plot the number in the list and set the line thickness.
            plt.plot(x_number_values, y_number_values, label=split(arg)[-1])

        # Set the line chart title and the text font size.
        plt.title(c['title'], fontsize=19)

        # Set x axes label.
        plt.xlabel("Time (s)", fontsize=10)

        # Set y axes label.
        # plt.ylabel("Size of input list", fontsize=10)

        plt.legend()

        # Set the x, y axis tick marks text size.
        # plt.tick_params(axis='both', labelsize=9)
        #plt.yticks( np.arange(0,100,10), np.arange(0,100,10))
        #plt.yticks( [], [])
        yticks = np.linspace(0,math.ceil(ymax),10,endpoint=True, dtype=c['type'])
        plt.yticks(yticks, yticks)
        ax.yaxis.set_major_formatter(ticker.FormatStrFormatter(c['format']))

        plt.grid()

        # Display the plot in the matplotlib's viewer.
        fig.savefig(c['col'].replace(' ','')+'.png')
        pdf.savefig()
        plt.close()
