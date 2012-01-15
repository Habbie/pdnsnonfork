/*
    PowerDNS Versatile Database Driven Nameserver
    Copyright (C) 2003 - 2011  PowerDNS.COM BV

    This program is free software; you can redistribute it and/or modify
    it under the terms of the GNU General Public License version 2 
    as published by the Free Software Foundation

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with this program; if not, write to the Free Software
    Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA  02110-1301  USA
*/
#include "json_ws.hh"
#include <boost/foreach.hpp>
#include <string>
#include "namespaces.hh"
#include <iostream>
#include "iputils.hh"

string returnJSONStats(const map<string, string>& items)
{
  ostringstream ostr;
  typedef map<string, string> map_t;
  ostr<<"{";
  for(map_t::const_iterator val = items.begin(); val != items.end(); ++val)
  {
    if(val != items.begin()) ostr<<", ";
    ostr << "\"" << val->first <<"\": \""<<val->second<<"\"\n";
  }
  ostr<<"}";
  return ostr.str();
}

JWebserver::JWebserver(FDMultiplexer* fdm) : d_fdm(fdm)
{
  d_socket = socket(AF_INET6, SOCK_STREAM, 0);
  setSocketReusable(d_socket);
  ComboAddress local("::", 8080);
  bind(d_socket, (struct sockaddr*)&local, local.getSocklen());
  listen(d_socket, 5);
  
  d_fdm->addReadFD(d_socket, boost::bind(&JWebserver::newConnection, this));
}

void JWebserver::readRequest(int fd)
{
  char buffer[16384];
  int res = read(fd, buffer, sizeof(buffer));
  if(res <= 0) {
    d_fdm->removeReadFD(fd);
    close(fd);
    cerr<<"Lost connection"<<endl;
  }
  buffer[res]=0;
  cerr<< buffer << endl;
  
  ostringstream ostr;
  ostr <<"23\r\n{\"epoch\":" << time(0)<<",\"daynum\":15308}\r\n0\r\n\r\n";
  
  char response[]="HTTP/1.1 200 OK\r\n"
  "Date: Wed, 30 Nov 2011 22:01:15 GMT\r\n"
  "Server: Apache/2.2.17 (Ubuntu)\r\n"
  "Connection: Keep-Alive\r\n"
  "Transfer-Encoding: chunked\r\n"
  "Access-Control-Allow-Origin: *\r\n"
  "Content-Type: application/json\r\n"
  "\r\n" ;
  
  write(fd, response, sizeof(response)-1);
  
  write(fd, ostr.str().c_str(), ostr.str().length());
}

void JWebserver::newConnection()
{
  
  ComboAddress remote;
  remote.sin4.sin_family=AF_INET6;
  socklen_t remlen = remote.getSocklen();
  int sock = accept(d_socket, (struct sockaddr*) &remote, &remlen);
  if(sock < 0)
    return;
    
  cerr<<"Connection from "<< remote.toStringWithPort() <<endl;
  Utility::setNonBlocking(sock);
  d_fdm->addReadFD(sock, boost::bind(&JWebserver::readRequest, this, _1));
}
