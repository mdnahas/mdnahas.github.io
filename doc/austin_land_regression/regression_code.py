#!/usr/bin/python3

import sys
#import csv
import pandas as pd 
import numpy as np
from statsmodels.formula.api import ols

# Read data
filename = sys.argv[1]
datos = pd.read_csv(filename)
df = pd.DataFrame(datos)

# removed dollarsigns
df['Price'] = df['Price'].str.replace(',', '')
df['Price'] = df['Price'].str.replace('$', '')
df['Price'] = df['Price'].astype('int')

# Remove bad data, extraneous data
# 12908 Wells Fargo ST --- there is no Wells Fargo St., but Google gave a lat-long.  And it's a bad outlier.
df = df[df.Address != "12908 Wells Fargo ST"]
# really long time  77882 seconds!
df = df[df.Address != "Toro Canyon & Via Media"]  
df = df[df.Acres > 0]
df = df[df.PropertySubType == "Single Lot"]

print(df)



# Need log fields
df['LogPrice'] = np.log10(df['Price'])
df['LogAcres'] = np.log10(df['Acres'])
df['LogPricePerAcres'] = np.log10(np.divide(df['Price'], df['Acres']))

# convert timestamps to number of years before/after reference date
# get median date
reference_date = int(np.median(pd.to_datetime(df["SaleDate"], format="%m/%d/%Y").astype(int)))
print("Reference date is " + str(pd.datetime.fromtimestamp(reference_date // (1000*1000*1000))))
nanos_in_year = 365.25*24*60*60*1000*1000*1000
df['SaleDateDiff'] = np.divide(np.subtract(pd.to_datetime(df["SaleDate"], format="%m/%d/%Y").astype(int), reference_date), nanos_in_year)


# The idea here is there are two "peaks" --- downtown and Lake Travis.
# The one around Lake Travis is not as high and might not be as steep.
# 
# This script tries to just to do the Austin side and stop before it gets
# to the Lake Travis affected area.
#
# Peak 2019: 2280
#      2014: 2280

#max_so_far = 0
#for edge_of_city in range(1650, 2450, 10):
edge_of_city = 2280

df = df[df.TimeSecs <= edge_of_city]

fit = ols('LogPricePerAcres ~ TimeSecs + LogAcres + 1', data=df).fit()
print(fit.summary())
#print("Slope = " + str(fit.params["TimeSecsCapped"]))

#if fit.rsquared > max_so_far:
#    max_so_far = fit.rsquared
#print(str(edge_of_city) + " -> " + str(fit.rsquared) + "    " + str(max_so_far))

#print(str(edge_of_city) + ", " + str(fit.rsquared) + ", " + str(fit.params["TimeSecs"]) + ", " + str(fit.params["LogAcres"]) + ", " + str(fit.params["Intercept"]))

    
print("Filename, Param, Value")
for k,v in fit.params.items():
    print(filename + ", " + str(k) + ", " + str(v))
print(filename + ", " + "EdgeOfCity" + ", " + str(edge_of_city))    

# log_ppa_eoc = (
#     fit.params["TimeSecsNear"]*edge_of_city
#     + fit.params["LogAcresNear"]*np.log10(1)
#     + fit.params["AcresTimeNear"]*np.log10(1)*edge_of_city
#     + fit.params["Intercept"])
# print("LogPricePerAcres at edge of city: " + str(log_ppa_eoc))


min_lot_size = 5750 / 43560

print("Filename, TimeSecs, LogPricePerAcreMinLot, PriceMinLot, LogPricePerOneAcre, PriceOneAcre")
for t in range(0, edge_of_city+60, 60):
    log_ppa_min = (
        fit.params["TimeSecs"]*t
        + fit.params["LogAcres"]*np.log10(min_lot_size)
        + fit.params["Intercept"])

    log_ppa_1acre = (
        fit.params["TimeSecs"]*t
        + fit.params["LogAcres"]*np.log10(1)
        + fit.params["Intercept"])

    print(str(filename) + ", " + str(t)
          + ", " + str(log_ppa_min) + "," + str(min_lot_size*10**log_ppa_min)
          + ", " +  str(log_ppa_1acre) + "," + str(1*10**log_ppa_1acre))
    
predictions = fit.predict(df)
df["predLogPrice"] = predictions
df['predPrice'] = np.power(10,df['predLogPrice'])
df.to_csv("predOnePeak_"+filename)
