import React from 'react';
import { useDrag } from 'react-dnd';
import { ListItemText, Tooltip, Typography, darken } from '@mui/material';

import AppointmentContainer from '../../container/Appointment';
import { getAppointmentDuration } from '../../utils/getAppointments';

function AppointmentItem(props) {
  const { appointment, width, height } = props;
  const classes = useStyles();

  const [{ isDragging }, drag] = useDrag({
    type: 'APPOINTMENT',
    item: { appointment },
    collect: (monitor) => ({
      isDragging: !!monitor.isDragging(),
    }),
  });

  const color = appointment.user.color;
  const duration = getAppointmentDuration(appointment.schedule);

  const apptItems = [
    `${appointment.id}: ${appointment.title}`,
    `${appointment.user.name} | Duration: ${duration}`,
  ];
  const tip = apptItems.join('\n');

  const tooltipMessage = <div style={classes.tooltip}>{tip}</div>;

  const primaryText = (
    <div style={classes.name}>
      {appointment.user.name}
      <span style={{ color: darken(color, 0.5) }}> | </span>
      Duration: {duration}
    </div>
  );

  const secondaryText = (
    <div style={classes.titleContainer}>
      <Typography sx={classes.id}>{appointment.id}:</Typography>
      <Typography variant='body2' sx={classes.title}>
        {appointment.title}
      </Typography>
    </div>
  );
  return (
    <AppointmentContainer
      key={appointment.id}
      ref={drag}
      isDragging={isDragging}
      height={height}
      width={width}
      appointmentColor={color}
    >
      <div style={classes.wrapper}>
        <Tooltip title={tooltipMessage}>
          <ListItemText primary={primaryText} secondary={secondaryText} />
        </Tooltip>
      </div>
    </AppointmentContainer>
  );
}

const useStyles = () => ({
  wrapper: {
    padding: 4,
  },
  titleContainer: {
    display: 'flex',
    alignItems: 'center',
  },
  title: {
    fontWeight: 'bold',
    marginLeft: 0.5,
    fontSize: '16px',
    textOverflow: 'ellipsis',
    whiteSpace: 'nowrap',
    overflow: 'hidden',
  },
  id: {
    fontSize: '400',
    fontSize: '16px',
    whiteSpace: 'nowrap',
  },
  name: {
    fontSize: '13px',
    textOverflow: 'ellipsis',
    whiteSpace: 'nowrap',
    overflow: 'hidden',
  },
  tooltip: {
    whiteSpace: 'pre-line',
    padding: 1,
  },
});

export default AppointmentItem;
