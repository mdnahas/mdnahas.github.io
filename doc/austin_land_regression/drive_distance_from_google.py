#!/usr/bin/python3

Google_API_key = "PUT YOUR GOOGLE API KEY HERE"

import csv
import sys
import time
import simplejson, urllib.request
import requests

def google_geocode(addr):
    url="https://maps.googleapis.com/maps/api/geocode/json?address={0},+Austin,+TX&key={1}".format(addr.replace(" ","+").replace("#","%23"), Google_API_key)
    try: 
        req = requests.get(url)
        try:
            result = req.json()
            if len(result["results"]) != 1:
                print("WARNING: had " + str(len(result["results"])) + " results for addr=" + addr, file=sys.stderr)
                return None
            latlng = result["results"][0]["geometry"]["location"]
            #print("Latlng: " + str(latlng))
            return latlng
        except:
            print("JSON failed for addr=" + addr, file=sys.stderr)
            print("request=" + str(req), file=sys.stderr)
            return None
    except:
        print("URL request failed for addr=" + addr, file=sys.stderr)
        print("URL=" + url, file=sys.stderr)
        return None
        

def google_distancematrix(loc1, loc2):
    loc1_str = str(loc1["lat"]) + "," + str(loc1["lng"])
    loc2_str = str(loc2["lat"]) + "," + str(loc2["lng"])
    # default mode is driving
    # arrival_time is seconds since 1970 UTC.  Maybe target 8:30am?
    # departure_time is seconds since 1970 UTC.  Maybe target 6pm?
    url="https://maps.googleapis.com/maps/api/distancematrix/json?units=imperial&origins={0}&destinations={1}&key={2}".format(loc1_str, loc2_str, Google_API_key)
    try: 
        req = requests.get(url)
        try:
            result = req.json()
            #print(str(result))
            if len(result["rows"]) != 1:
                print("WARNING: had " + str(len(result["rows"])) + " rows for loc1=" + loc1_str + " loc2=" + loc2_str, file=sys.stderr)
                return None
            if len(result["rows"][0]["elements"]) != 1:
                print("WARNING: had " + str(len(result["rows"][0]["elements"])) + " elements for loc1=" + loc1_str + " loc2=" + loc2_str, file=sys.stderr)
                return None
            retval = {}
            retval["feet"] = result["rows"][0]["elements"][0]["distance"]["value"]
            retval["secs"] = result["rows"][0]["elements"][0]["duration"]["value"]
            #print("retval: " + str(retval))
            return retval
        except:
            print("JSON failed for loc1=" + loc1_str + " loc2=" + loc2_str, file=sys.stderr)
            print("request=" + str(req), file=sys.stderr)
            return None
    except:
        print("URL request failed for loc1=" + loc1_str + " loc2=" + loc2_str, file=sys.stderr)
        print("URL=" + url, file=sys.stderr)
        return None
        

# central business district location
CBD_Address = "515 Congress Ave"
CBD_location = google_geocode(CBD_Address)
#print(CBD_location)
#CBD_latlng_pair = ( CBD_location["lat"] , CBD_location["lng"])

filename = sys.argv[1]
fieldnames = "Address","OTHER FIELDS","TimeSecs","DistFeet"

with open(filename, 'r') as csvfile:
    csv_reader = csv.DictReader(csvfile)
    csv_writer = csv.DictWriter(sys.stdout, fieldnames=fieldnames, extrasaction='ignore')
    csv_writer.writeheader()
    for row in csv_reader:
        print("Processing " + row["Address"], file=sys.stderr)

        location = google_geocode(row["Address"])
        
        # Would love driving distance using OSRM.
        # Instead, using crow-flies distance
        if location is None:
            print("Error with address " + row["Address"], file=sys.stderr)
            continue
        
        time_dist = google_distancematrix(location, CBD_location)

        row["DistFeet"] = time_dist["feet"]
        row["TimeSecs"] = time_dist["secs"]
        
        csv_writer.writerow(row)

        time.sleep(0.1)








# import simplejson, urllib
# orig_coord = str(location.latitude) + "," + str(location.longitude)
# dest_coord = str(CBD_location.latitude) + "," + str(CBD_location.longitude)
# url = "https://maps.googleapis.com/maps/api/distancematrix/json?key={2}&origins={0}&destinations={1}&mode=driving&language=en-EN&sensor=false".format(orig_coord,dest_coord, Google_API_key)
# result= simplejson.load(urllib.request.urlopen(url))
# driving_time = result['rows'][0]['elements'][0]['duration']['value']


#'http://maps.googleapis.com/maps/api/distancematrix/json?origins=30.348107,-97.778725&destinations=30.267679,-97.742479&mode=driving&language=en-EN&sensor=false'
