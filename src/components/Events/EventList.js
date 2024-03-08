import React from 'react'
import EventItem from './EventItem';

function EventList(props) {
  const {
    unscheduledList,
    appointmentList
  } = props;

  return (
    <div style={{width: '100px', border: 'solid 1px black', marginRight: '12px'}} >
    {
        unscheduledList.filter(appointment => {
          return !appointmentList.some(item => item.id === appointment.id);
        }).map((item) => (
            <EventItem key={item.id} appointment={item} />
          ))
    }
    </div>
  )
}

export default EventList