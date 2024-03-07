import PropTypes from 'prop-types';

export const AppointmentPropTypes = PropTypes.shape({
    /**
     * Set the background color for the appointment when it is being dragged
     */
    dragBgColor: PropTypes.string,
     /**
     * You can override the styles
     */
    style: PropTypes.object
});

export const AppointmentDefaultValue = {
    dragBgColor: '#E0E0E0',
    style: {}
}